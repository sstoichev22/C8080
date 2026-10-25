package C8080;

import static C8080.Parser.*;
import static C8080.Token.TokenType.*;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.CancellationException;
import java.util.function.BooleanSupplier;

/** Builds fail-closed semantic refactoring previews from immutable project text, without writing files.
 * Ordinary function and object names are supported. Members, types, enumerators, macros and assembly names are not.
 * External identities cross translation units only through a shared physical declaration in an included header;
 * equal spellings in independent programs are never sufficient evidence. All translation units must parse.
 */
public final class SourceRefactoring {
    /** Supported source transformations; numeric extraction and inlining are restricted to block-local scalar values. */
    public enum Operation { RENAME, INTRODUCE_VARIABLE, INLINE_VARIABLE }

    /** Immutable inputs. Paths are normalized absolute paths; offsets are UTF-16, with an exclusive selection end.
     * The source map must contain all project translation units and their unsaved include texts. Missing includes fail.
     * Include directories are searched in order. The root bounds editable files, not readable include snapshots.
     * A zero-length selection selects an identifier at the caret; extraction requires an exact expression selection.
     */
    public record Request(Map<Path, String> sources, Path root, List<Path> includeDirectories, Path selectedPath,
            int selectionStart, int selectionEnd, Operation operation, String replacementName) {
        public Request {
            Objects.requireNonNull(sources, "sources");
            Map<Path, String> copied = new LinkedHashMap<>();
            sources.forEach((path, text) -> {
                Path normalized = normalize(path);
                if (copied.put(normalized, Objects.requireNonNull(text, "source text")) != null)
                    throw new IllegalArgumentException("Duplicate normalized source path: " + normalized);
            });
            sources = Collections.unmodifiableMap(copied);
            root = normalize(root);
            includeDirectories = includeDirectories.stream().map(SourceRefactoring::normalize).toList();
            selectedPath = normalize(selectedPath);
            operation = Objects.requireNonNull(operation, "operation");
            replacementName = replacementName == null ? "" : replacementName;
            String selected = sources.get(selectedPath);
            if (selected == null || selectionStart < 0 || selectionEnd < selectionStart || selectionEnd > selected.length())
                throw new IllegalArgumentException("Selection is not within a source snapshot.");
        }
    }

    /** Whole-file optimistic edit. The caller must verify expectedText before applying updatedText atomically. */
    public record FileEdit(Path path, String expectedText, String updatedText) {}
    /** A safety failure at a UTF-16 source offset; no preview containing a conflict may be applied. */
    public record Conflict(Path path, int offset, String message) {}
    /** Immutable all-or-nothing preview. Conflicted previews never expose partial edits. */
    public record Preview(List<FileEdit> edits, List<Conflict> conflicts) {
        public Preview {
            edits = List.copyOf(edits);
            conflicts = List.copyOf(conflicts);
            if (!conflicts.isEmpty()) edits = List.of();
        }
        /** Returns true only when there are actual changes and no safety failures. */
        public boolean applicable() { return conflicts.isEmpty() && !edits.isEmpty(); }
    }

    private record Range(Path path, int start, int end) {}
    private record Change(Range range, String text) {}
    private record RawIdentifier(String name, Range range) {}
    private record Binding(Symbol symbol, int start) {}
    private record Use(Translation translation, Object node, Token token, Symbol symbol, Scope scope,
            boolean declaration, boolean write, boolean address) {}
    private record ExpressionSite(Translation translation, Expr expression, Stmt anchor, Scope scope) {}

    private static final class Symbol {
        final String name;
        final boolean external;
        final Object declaration;
        final Scope scope;
        final CType type;
        Symbol parent = this;
        Symbol(String name, boolean external, Object declaration, Scope scope, CType type) {
            this.name = name;
            this.external = external;
            this.declaration = declaration;
            this.scope = scope;
            this.type = type;
        }
        Symbol identity() {
            if (parent != this) parent = parent.identity();
            return parent;
        }
    }

    private static final class Scope {
        final Scope parent;
        final Map<String, List<Binding>> bindings = new LinkedHashMap<>();
        Scope(Scope parent) { this.parent = parent; }
        void add(Symbol symbol, int start) {
            bindings.computeIfAbsent(symbol.name, ignored -> new ArrayList<>()).add(new Binding(symbol, start));
        }
        Symbol resolve(String name, int at, Symbol renamed, String replacement) {
            for (Scope current = this; current != null; current = current.parent) {
                Binding found = null;
                for (List<Binding> values : current.bindings.values()) for (Binding binding : values) {
                    Symbol identity = binding.symbol.identity();
                    String effective = renamed != null && identity == renamed ? replacement : binding.symbol.name;
                    if (effective.equals(name) && binding.start <= at && (found == null || binding.start > found.start))
                        found = binding;
                }
                if (found != null) return found.symbol.identity();
            }
            return null;
        }
    }

    private static final class Translation {
        final Path path;
        final Preprocessor preprocessor;
        final Parser parser;
        final Unit unit;
        final List<Token> tokens;
        final Map<Token, Integer> order = new IdentityHashMap<>();
        final Scope global = new Scope(null);
        final Map<Object, Symbol> declarations = new IdentityHashMap<>();
        final Set<Path> included = new LinkedHashSet<>();
        final List<Use> uses = new ArrayList<>();
        final List<ExpressionSite> expressions = new ArrayList<>();
        final Map<DeclStmt, Stmt> declarationStatements = new IdentityHashMap<>();
        Translation(Path path, Preprocessor preprocessor, Parser parser, Unit unit, List<Token> tokens) {
            this.path = path;
            this.preprocessor = preprocessor;
            this.parser = parser;
            this.unit = unit;
            this.tokens = tokens;
            for (int n = 0; n < tokens.size(); n++) order.put(tokens.get(n), n);
            for (Preprocessor.SourceLine line : preprocessor.sourceLines()) if (line.path() != null) included.add(line.path());
            included.add(path);
        }
        int at(Token token) { return token == null ? -1 : order.getOrDefault(token, -1); }
    }

    private final Request request;
    private final BooleanSupplier cancelled;
    private final List<Translation> translations = new ArrayList<>();
    private final List<Conflict> conflicts = new ArrayList<>();
    private final Map<Path, int[]> lineStarts = new LinkedHashMap<>();
    private final Map<Path, List<RawIdentifier>> raw = new LinkedHashMap<>();
    private final List<Change> changes = new ArrayList<>();

    private SourceRefactoring(Request request, BooleanSupplier cancelled) {
        this.request = Objects.requireNonNull(request, "request");
        this.cancelled = cancelled == null ? () -> false : cancelled;
    }

    /** Returns a semantic preview without changing any source, file or global compiler state. */
    public static Preview preview(Request request) { return preview(request, () -> false); }

    /** Returns a semantic preview, polling cancellation during lexing, preprocessing, binding and editing.
     * @throws CancellationException when cancellation is requested; no partial edits are returned
     */
    public static Preview preview(Request request, BooleanSupplier cancelled) {
        return new SourceRefactoring(request, cancelled).run();
    }

    private Preview run() {
        checkpoint();
        if (request.operation != Operation.INLINE_VARIABLE && !validName(request.replacementName)) {
            conflict(request.selectedPath, request.selectionStart, "Replacement must be a non-keyword C identifier.");
            return result();
        }
        parseProject();
        if (!conflicts.isEmpty()) return result();
        bindProject();
        if (!conflicts.isEmpty()) return result();
        if (request.operation == Operation.INTRODUCE_VARIABLE) introduce();
        else {
            Symbol selected = selectedSymbol();
            if (selected != null) {
                if (request.operation == Operation.RENAME) rename(selected);
                else inline(selected);
            }
        }
        if (conflicts.isEmpty() && !changes.isEmpty()) validateUpdatedSources();
        return result();
    }

    private void parseProject() {
        List<Path> units = request.sources.keySet().stream().filter(SourceRefactoring::isTranslationUnit).toList();
        if (units.isEmpty()) units = List.of(request.selectedPath);
        for (Path path : units) {
            checkpoint();
            try {
                Preprocessor preprocessor = new Preprocessor(request.includeDirectories, include -> request.sources.get(include));
                String expanded = preprocessor.process(withoutBom(request.sources.get(path)), path, cancelled);
                List<Token> tokens = new Lexer(expanded).tokenize(cancelled);
                Parser parser = new Parser(tokens, cancelled);
                Unit unit = parser.parse(cancelled);
                translations.add(new Translation(path, preprocessor, parser, unit, tokens));
            } catch (IllegalArgumentException error) {
                conflict(path, 0, "Cannot prove refactoring safe because parsing failed: " + error.getMessage());
            }
        }
    }

    private void bindProject() {
        Map<Range, Symbol> sharedDeclarations = new LinkedHashMap<>();
        for (Translation translation : translations) {
            checkpoint();
            List<Object> declarations = new ArrayList<>(translation.unit.globals());
            declarations.addAll(translation.unit.functions());
            declarations.sort(Comparator.comparingInt(node -> translation.at(translation.parser.identifiers().get(node))));
            for (Object node : declarations) {
                String name = node instanceof Function f ? f.name() : ((DeclStmt) node).name();
                Storage storage = node instanceof Function f ? f.storage() : ((DeclStmt) node).storage();
                CType type = node instanceof Function f ? CType.function(f.type(), f.parameters().stream().map(DeclStmt::type).toList(), f.variadic())
                        : ((DeclStmt) node).type();
                Token token = translation.parser.identifiers().get(node);
                Symbol prior = translation.global.resolve(name, Integer.MAX_VALUE, null, "");
                boolean external = storage != Storage.STATIC;
                Symbol symbol = new Symbol(name, external, node, translation.global, type);
                if (prior != null) {
                    if (prior.external != external || !prior.type.sameDeclaration(type))
                        conflict(translation.path, 0, "Incompatible declarations prevent safe binding of " + name + ".");
                    else symbol.parent = prior.identity();
                }
                translation.global.add(symbol, translation.at(token));
                translation.declarations.put(node, symbol);
                addUse(translation, node, token, symbol, translation.global, true, false, false);
                if (external) {
                    Range range = mapped(translation, token, false);
                    if (range != null && !isTranslationUnit(range.path)) {
                        Symbol shared = sharedDeclarations.putIfAbsent(range, symbol);
                        if (shared != null) {
                            if (!shared.type.sameDeclaration(type)) conflict(range.path, range.start, "Shared declaration has incompatible types.");
                            else symbol.identity().parent = shared.identity();
                        }
                    }
                }
            }
            for (DeclStmt global : translation.unit.globals()) walkExpr(translation, global.initializer(), translation.global, null, false, false);
            for (Function function : translation.unit.functions()) {
                Scope parameters = new Scope(translation.global);
                for (DeclStmt parameter : function.parameters()) {
                    Symbol symbol = new Symbol(parameter.name(), false, parameter, parameters, parameter.type());
                    Token token = translation.parser.identifiers().get(parameter);
                    parameters.add(symbol, translation.at(token));
                    translation.declarations.put(parameter, symbol);
                    if (token != null) addUse(translation, parameter, token, symbol, parameters, true, false, false);
                }
                if (function.body() != null) walkBlock(translation, function.body(), parameters, true);
            }
        }
    }

    private void walkBlock(Translation translation, BlockStmt block, Scope enclosing, boolean functionBody) {
        Scope scope = functionBody ? enclosing : new Scope(enclosing);
        for (Stmt statement : block.statements()) walkStmt(translation, statement, scope, statement);
    }

    private void walkStmt(Translation t, Stmt statement, Scope scope, Stmt anchor) {
        checkpoint();
        if (statement == null) return;
        if (statement instanceof BlockStmt block) walkBlock(t, block, scope, false);
        else if (statement instanceof DeclGroup group) {
            for (DeclStmt declaration : group.declarations()) declareLocal(t, declaration, scope, anchor, statement);
        } else if (statement instanceof DeclStmt declaration) declareLocal(t, declaration, scope, anchor, statement);
        else if (statement instanceof ExprStmt expression) walkExpr(t, expression.value(), scope, anchor, false, false);
        else if (statement instanceof ReturnStmt returned) walkExpr(t, returned.value(), scope, anchor, false, false);
        else if (statement instanceof IfStmt conditional) {
            walkExpr(t, conditional.condition(), scope, anchor, false, false);
            walkStmt(t, conditional.yes(), scope, anchor);
            walkStmt(t, conditional.no(), scope, anchor);
        } else if (statement instanceof WhileStmt loop) {
            walkExpr(t, loop.condition(), scope, anchor, false, false);
            walkStmt(t, loop.body(), scope, anchor);
        } else if (statement instanceof DoWhileStmt loop) {
            walkStmt(t, loop.body(), scope, anchor);
            walkExpr(t, loop.condition(), scope, anchor, false, false);
        } else if (statement instanceof ForStmt loop) {
            Scope forScope = new Scope(scope);
            walkStmt(t, loop.init(), forScope, anchor);
            walkExpr(t, loop.condition(), forScope, anchor, false, false);
            walkExpr(t, loop.update(), forScope, anchor, false, false);
            walkStmt(t, loop.body(), forScope, anchor);
        } else if (statement instanceof SwitchStmt switched) {
            walkExpr(t, switched.value(), scope, anchor, false, false);
            Scope switchScope = new Scope(scope);
            for (SwitchCase branch : switched.cases()) for (Stmt child : branch.statements()) walkStmt(t, child, switchScope, anchor);
        }
    }

    private void declareLocal(Translation t, DeclStmt declaration, Scope scope, Stmt anchor, Stmt statement) {
        Token token = t.parser.identifiers().get(declaration);
        Symbol symbol = new Symbol(declaration.name(), false, declaration, scope, declaration.type());
        scope.add(symbol, t.at(token));
        t.declarations.put(declaration, symbol);
        t.declarationStatements.put(declaration, statement == anchor ? statement : null);
        addUse(t, declaration, token, symbol, scope, true, false, false);
        walkExpr(t, declaration.initializer(), scope, anchor, false, false);
    }

    private void walkExpr(Translation t, Expr expression, Scope scope, Stmt anchor, boolean write, boolean address) {
        if (expression == null) return;
        checkpoint();
        t.expressions.add(new ExpressionSite(t, expression, anchor, scope));
        if (expression instanceof VariableExpr variable) {
            Token token = t.parser.identifiers().get(variable);
            Symbol symbol = scope.resolve(variable.name(), t.at(token), null, "");
            addUse(t, variable, token, symbol, scope, false, write, address);
        } else if (expression instanceof UnaryExpr unary) {
            walkExpr(t, unary.value(), scope, anchor, false, address || unary.op() == AMP);
        } else if (expression instanceof BinaryExpr binary) {
            walkExpr(t, binary.left(), scope, anchor, false, false);
            walkExpr(t, binary.right(), scope, anchor, false, false);
        } else if (expression instanceof AssignExpr assignment) {
            walkExpr(t, assignment.target(), scope, anchor, true, false);
            walkExpr(t, assignment.value(), scope, anchor, false, false);
        } else if (expression instanceof UpdateExpr update) walkExpr(t, update.target(), scope, anchor, true, false);
        else if (expression instanceof CallExpr call) {
            walkExpr(t, call.callee(), scope, anchor, false, false);
            for (Expr argument : call.arguments()) walkExpr(t, argument, scope, anchor, false, false);
        } else if (expression instanceof MemberExpr member) walkExpr(t, member.base(), scope, anchor, write, address);
        else if (expression instanceof IndexExpr index) {
            walkExpr(t, index.base(), scope, anchor, false, address);
            walkExpr(t, index.index(), scope, anchor, false, false);
        } else if (expression instanceof CastExpr cast) walkExpr(t, cast.value(), scope, anchor, write, address);
        else if (expression instanceof SizeofExpr size) walkExpr(t, size.value(), scope, anchor, false, false);
        else if (expression instanceof InitListExpr list) {
            for (Expr item : list.values()) walkExpr(t, item, scope, anchor, false, false);
        } else if (expression instanceof ConditionalExpr conditional) {
            walkExpr(t, conditional.condition(), scope, anchor, false, false);
            walkExpr(t, conditional.yes(), scope, anchor, write, address);
            walkExpr(t, conditional.no(), scope, anchor, write, address);
        } else if (expression instanceof CommaExpr comma) {
            walkExpr(t, comma.left(), scope, anchor, false, false);
            walkExpr(t, comma.right(), scope, anchor, write, address);
        }
    }

    private void addUse(Translation t, Object node, Token token, Symbol symbol, Scope scope,
            boolean declaration, boolean write, boolean address) {
        if (token != null) t.uses.add(new Use(t, node, token, symbol, scope, declaration, write, address));
    }

    private Symbol selectedSymbol() {
        Symbol selected = null;
        for (Translation translation : translations) for (Use use : translation.uses) {
            Range range = mapped(translation, use.token, false);
            if (range != null && selected(range)) {
                if (use.symbol == null) {
                    conflict(range.path, range.start, "Selected identifier has no visible declaration.");
                    return null;
                }
                Symbol identity = use.symbol.identity();
                if (selected != null && selected != identity) {
                    conflict(range.path, range.start, "This source identifier binds differently in multiple include contexts.");
                    return null;
                }
                selected = identity;
            }
        }
        if (selected == null) conflict(request.selectedPath, request.selectionStart,
                "Select an ordinary function, parameter or variable identifier; types, members, macros and enumerators are unsupported.");
        return selected;
    }

    private void rename(Symbol target) {
        String replacement = request.replacementName;
        if (replacement.equals(target.name)) {
            conflict(request.selectedPath, request.selectionStart, "The replacement name is unchanged.");
            return;
        }
        List<Use> targetUses = uses(target);
        Set<Translation> affected = affected(targetUses);
        for (Translation translation : affected) {
            checkpoint();
            for (Use use : translation.uses) {
                if (use.symbol == null) {
                    if (use.token.data.equals(target.name) || use.token.data.equals(replacement))
                        conflict(translation.path, 0, "An unresolved reference could change binding: " + use.token.data + ".");
                    continue;
                }
                if (use.declaration) {
                    if (use.symbol.identity() == target) {
                        for (List<Binding> values : use.scope.bindings.values()) for (Binding binding : values)
                            if (binding.symbol.identity() != target && binding.symbol.name.equals(replacement))
                                conflict(translation.path, 0, "The replacement collides with a declaration in the same scope.");
                    }
                    continue;
                }
                String effective = use.symbol.identity() == target ? replacement : use.token.data;
                Symbol after = use.scope.resolve(effective, translation.at(use.token), target, replacement);
                if (after != use.symbol.identity()) conflict(translation.path, 0, "Renaming would capture or redirect a reference to " + effective + ".");
            }
        }
        checkPhysicalContexts(target, targetUses);
        checkUnmappedIdentifiers(affected, target.name, replacement);
        for (Use use : targetUses) {
            if (use.symbol.declaration instanceof DeclStmt declaration && declaration.storage() == Storage.EXTERN && use.symbol.scope.parent != null)
                conflict(use.translation.path, 0, "Block-scope extern declarations are not supported by this refactoring.");
            Range range = mapped(use.translation, use.token, true);
            if (range != null) change(range, replacement);
        }
    }

    private void checkPhysicalContexts(Symbol target, List<Use> targetUses) {
        Set<Range> ranges = new LinkedHashSet<>();
        for (Use use : targetUses) {
            Range range = mapped(use.translation, use.token, false);
            if (range != null) ranges.add(range);
        }
        for (Translation translation : translations) for (Use use : translation.uses) {
            Range range = mapped(translation, use.token, false);
            if (range != null && ranges.contains(range) && (use.symbol == null || use.symbol.identity() != target))
                conflict(range.path, range.start, "One physical identifier has different semantic bindings in different translation units.");
        }
    }

    private void checkUnmappedIdentifiers(Set<Translation> affected, String oldName, String newName) {
        Map<Path, Set<Range>> covered = new LinkedHashMap<>();
        Set<Path> paths = new LinkedHashSet<>();
        for (Translation translation : affected) {
            paths.addAll(translation.included);
            for (Token token : translation.tokens) if (token.type == IDENTIFIER) {
                Range range = mapped(translation, token, false);
                if (range != null && translation.preprocessor.isDirectLocation(token.line, token.column, token.data.length()))
                    covered.computeIfAbsent(range.path, ignored -> new LinkedHashSet<>()).add(range);
            }
        }
        for (Path path : paths) for (RawIdentifier identifier : rawIdentifiers(path)) {
            if ((identifier.name.equals(oldName) || identifier.name.equals(newName))
                    && !covered.getOrDefault(path, Set.of()).contains(identifier.range))
                conflict(path, identifier.range.start, "A macro, inactive branch, assembly target or unsupported identifier prevents safe refactoring: " + identifier.name + ".");
        }
    }

    private void introduce() {
        if (request.selectionStart == request.selectionEnd) {
            conflict(request.selectedPath, request.selectionStart, "Select a complete numeric constant expression.");
            return;
        }
        ExpressionSite selected = null;
        for (Translation translation : translations) for (ExpressionSite site : translation.expressions) {
            Range range = span(translation, site.expression, false);
            if (range != null && range.path.equals(request.selectedPath) && range.start == request.selectionStart && range.end == request.selectionEnd) {
                if (selected != null && selected.translation != translation) {
                    conflict(range.path, range.start, "Expression extraction in shared include contexts is unsupported.");
                    return;
                }
                selected = site;
            }
        }
        if (selected == null || selected.anchor == null || !numeric(selected.expression)) {
            conflict(request.selectedPath, request.selectionStart, "Only a complete numeric constant expression within a block statement can be extracted.");
            return;
        }
        Translation translation = selected.translation;
        CType type;
        try { type = ConstantEvaluator.evaluate(selected.expression, cancelled).type(); }
        catch (IllegalArgumentException error) {
            conflict(request.selectedPath, request.selectionStart, "The expression is not a safe numeric constant: " + error.getMessage());
            return;
        }
        if (selected.anchor instanceof DeclGroup group && group.declarations().stream().anyMatch(declaration -> declaration.storage() != Storage.AUTO)) {
            conflict(request.selectedPath, request.selectionStart, "Extraction cannot change static or external initializer constant requirements.");
            return;
        }
        Range expression = span(translation, selected.expression, true);
        Range anchor = span(translation, selected.anchor, true);
        if (expression == null || anchor == null) return;
        checkUnmappedIdentifiers(Set.of(translation), "", request.replacementName);
        for (RawIdentifier identifier : rawIdentifiers(request.selectedPath)) if (identifier.name.equals(request.replacementName))
            conflict(identifier.range.path, identifier.range.start, "The introduced name already occurs in this source file.");
        if (!anchor.path.equals(expression.path)) {
            conflict(expression.path, expression.start, "Extraction must stay in one physical source file.");
            return;
        }
        String source = request.sources.get(expression.path);
        String newline = source.contains("\r\n") ? "\r\n" : source.contains("\r") ? "\r" : "\n";
        int lineStart = anchor.start;
        while (lineStart > 0 && source.charAt(lineStart - 1) != '\n' && source.charAt(lineStart - 1) != '\r') lineStart--;
        String indentation = source.substring(lineStart, anchor.start);
        if (!indentation.isBlank()) indentation = "";
        String declaration = typeName(type) + " " + request.replacementName + " = " + source.substring(expression.start, expression.end) + ";" + newline + indentation;
        change(new Range(anchor.path, anchor.start, anchor.start), declaration);
        change(expression, request.replacementName);
    }

    private void inline(Symbol target) {
        if (!(target.declaration instanceof DeclStmt declaration) || target.scope.parent == null
                || declaration.storage() != Storage.AUTO || declaration.type().volatileQualified
                || !scalar(declaration.type()) || declaration.initializer() == null || !numeric(declaration.initializer())) {
            conflict(request.selectedPath, request.selectionStart, "Only a non-volatile scalar automatic local with a numeric constant initializer can be inlined.");
            return;
        }
        List<Use> uses = uses(target);
        Set<Translation> affected = affected(uses);
        if (affected.size() != 1) {
            conflict(request.selectedPath, request.selectionStart, "Inlining across include contexts is unsupported.");
            return;
        }
        Translation translation = affected.iterator().next();
        Stmt statement = translation.declarationStatements.get(declaration);
        if (!(statement instanceof DeclGroup group) || group.declarations().size() != 1) {
            conflict(request.selectedPath, request.selectionStart, "Inline requires a single declaration directly in a block, not a for initializer or declaration group.");
            return;
        }
        try { ConstantEvaluator.evaluate(declaration.initializer(), cancelled).convert(declaration.type()); }
        catch (IllegalArgumentException error) {
            conflict(request.selectedPath, request.selectionStart, "Initializer cannot be safely evaluated: " + error.getMessage());
            return;
        }
        Range initializer = span(translation, declaration.initializer(), true);
        Range declarationRange = span(translation, statement, true);
        if (initializer == null || declarationRange == null) return;
        checkUnmappedIdentifiers(affected, target.name, "");
        checkPhysicalContexts(target, uses);
        String source = request.sources.get(initializer.path);
        String replacement = "((" + typeName(declaration.type()) + ")(" + source.substring(initializer.start, initializer.end) + "))";
        int references = 0;
        for (Use use : uses) if (!use.declaration) {
            if (use.write || use.address) conflict(translation.path, 0, "The local is written or its address escapes; it cannot be inlined.");
            Range range = mapped(translation, use.token, true);
            if (range != null) change(range, replacement);
            references++;
        }
        if (references == 0) conflict(request.selectedPath, request.selectionStart, "The local has no references to inline.");
        change(declarationRange, "");
    }

    private static boolean scalar(CType type) { return type.kind == CType.Kind.INTEGER || type.kind == CType.Kind.FLOAT; }

    private boolean numeric(Expr expression) {
        checkpoint();
        if (expression instanceof NumberExpr || expression instanceof FloatExpr) return true;
        if (expression instanceof UnaryExpr unary) return unary.op() != AMP && unary.op() != STAR && numeric(unary.value());
        if (expression instanceof BinaryExpr binary) return numeric(binary.left()) && numeric(binary.right());
        if (expression instanceof CastExpr cast) return scalar(cast.type()) && !cast.type().volatileQualified && numeric(cast.value());
        if (expression instanceof ConditionalExpr conditional)
            return numeric(conditional.condition()) && numeric(conditional.yes()) && numeric(conditional.no());
        return false;
    }

    private static String typeName(CType type) {
        if (type.kind == CType.Kind.FLOAT) return type.size == 4 ? "float" : "double";
        return type.isBoolean() ? "bool" : type.name;
    }

    private List<Use> uses(Symbol symbol) {
        List<Use> result = new ArrayList<>();
        for (Translation translation : translations) for (Use use : translation.uses)
            if (use.symbol != null && use.symbol.identity() == symbol) result.add(use);
        return result;
    }

    private static Set<Translation> affected(List<Use> uses) {
        Set<Translation> result = new LinkedHashSet<>();
        for (Use use : uses) result.add(use.translation);
        return result;
    }

    private Range mapped(Translation translation, Token token, boolean requireDirect) {
        if (token == null) return null;
        Preprocessor.MappedLocation location = translation.preprocessor.mapLocation(token.line, token.column, Math.max(1, token.data.length()));
        if (location == null || location.source().path() == null) return null;
        Path path = normalize(location.source().path());
        String source = request.sources.get(path);
        if (source == null) {
            if (requireDirect) conflict(path, 0, "Required source is not part of the immutable snapshot.");
            return null;
        }
        int[] starts = lineStarts.computeIfAbsent(path, ignored -> starts(source));
        int line = location.source().line() - 1;
        if (line < 0 || line >= starts.length) return null;
        int start = starts[line] + location.column() - 1;
        int end = start + location.length();
        if (start < 0 || end > source.length()) return null;
        Range result = new Range(path, start, end);
        if (requireDirect && (!translation.preprocessor.isDirectLocation(token.line, token.column, Math.max(1, token.data.length()))
                || !source.substring(start, end).equals(token.data))) {
            conflict(path, start, "A required identifier or expression token is macro-generated, spliced or non-bijective.");
            return null;
        }
        return result;
    }

    private Range span(Translation translation, Object node, boolean requireDirect) {
        SourceSpan span = translation.parser.spans().get(node);
        if (span == null) return null;
        Range first = mapped(translation, span.first(), requireDirect);
        Range last = mapped(translation, span.last(), requireDirect);
        if (first == null || last == null || !first.path.equals(last.path) || first.start > last.end) return null;
        if (requireDirect) {
            int previousEnd = first.start;
            for (int n = translation.at(span.first()); n <= translation.at(span.last()); n++) {
                Range token = mapped(translation, translation.tokens.get(n), true);
                if (token == null || !token.path.equals(first.path) || token.start < previousEnd) {
                    conflict(first.path, first.start, "The selected source span crosses an include or ambiguous preprocessing boundary.");
                    return null;
                }
                previousEnd = token.end;
            }
        }
        return new Range(first.path, first.start, last.end);
    }

    private boolean selected(Range range) {
        if (!range.path.equals(request.selectedPath)) return false;
        if (request.selectionStart == request.selectionEnd)
            return request.selectionStart >= range.start && request.selectionStart < range.end;
        return request.selectionStart == range.start && request.selectionEnd == range.end;
    }

    private void change(Range range, String text) {
        checkpoint();
        if (!editable(range.path)) {
            conflict(range.path, range.start, "A required edit is outside the project root or belongs to a read-only source.");
            return;
        }
        Change change = new Change(range, text);
        if (!changes.contains(change)) changes.add(change);
    }

    private boolean editable(Path path) {
        if (!path.startsWith(request.root)) return false;
        for (Path segment : request.root.relativize(path)) if (segment.toString().equalsIgnoreCase("sources")) return false;
        try {
            if (Files.exists(path)) {
                if (!Files.isWritable(path)) return false;
                Path realRoot = Files.exists(request.root) ? request.root.toRealPath() : request.root;
                if (!path.toRealPath().startsWith(realRoot)) return false;
                if (Files.getFileStore(path).supportsFileAttributeView("dos")
                        && Files.readAttributes(path, java.nio.file.attribute.DosFileAttributes.class).isReadOnly()) return false;
            }
        } catch (IOException | SecurityException error) {
            return false;
        }
        return true;
    }

    private Map<Path, String> updatedSources() {
        Map<Path, String> updated = new LinkedHashMap<>(request.sources);
        Map<Path, List<Change>> grouped = new LinkedHashMap<>();
        for (Change change : changes) grouped.computeIfAbsent(change.range.path, ignored -> new ArrayList<>()).add(change);
        for (Map.Entry<Path, List<Change>> entry : grouped.entrySet()) {
            List<Change> fileChanges = entry.getValue();
            fileChanges.sort(Comparator.comparingInt((Change change) -> change.range.start).thenComparingInt(change -> change.range.end));
            int end = -1;
            for (Change change : fileChanges) {
                if (change.range.start < end) {
                    conflict(entry.getKey(), change.range.start, "Overlapping semantic edits prevent a safe preview.");
                    return updated;
                }
                end = change.range.end;
            }
            StringBuilder source = new StringBuilder(request.sources.get(entry.getKey()));
            for (int n = fileChanges.size() - 1; n >= 0; n--) {
                checkpoint();
                Change change = fileChanges.get(n);
                source.replace(change.range.start, change.range.end, change.text);
            }
            updated.put(entry.getKey(), source.toString());
        }
        return updated;
    }

    private void validateUpdatedSources() {
        Map<Path, String> updated = updatedSources();
        if (!conflicts.isEmpty()) return;
        for (Translation translation : translations) {
            checkpoint();
            try {
                Preprocessor preprocessor = new Preprocessor(request.includeDirectories, updated::get);
                String expanded = preprocessor.process(withoutBom(updated.get(translation.path)), translation.path, cancelled);
                new Parser(new Lexer(expanded).tokenize(cancelled), cancelled).parse(cancelled);
            } catch (IllegalArgumentException error) {
                conflict(translation.path, 0, "The transformed translation unit does not parse: " + error.getMessage());
            }
        }
    }

    private Preview result() {
        checkpoint();
        if (!conflicts.isEmpty()) return new Preview(List.of(), conflicts);
        Map<Path, String> updated = updatedSources();
        List<FileEdit> edits = new ArrayList<>();
        updated.forEach((path, text) -> {
            if (!text.equals(request.sources.get(path))) edits.add(new FileEdit(path, request.sources.get(path), text));
        });
        return new Preview(edits, conflicts);
    }

    private List<RawIdentifier> rawIdentifiers(Path path) {
        return raw.computeIfAbsent(path, key -> {
            String source = request.sources.getOrDefault(key, "");
            List<RawIdentifier> result = new ArrayList<>();
            for (int n = 0; n < source.length();) {
                checkpoint();
                char c = source.charAt(n);
                if (c == '"' || c == '\'') {
                    char quote = c;
                    n++;
                    while (n < source.length()) {
                        char next = source.charAt(n++);
                        if (next == '\\' && n < source.length()) n++;
                        else if (next == quote) break;
                    }
                } else if (c == '/' && n + 1 < source.length() && source.charAt(n + 1) == '/') {
                    n += 2;
                    while (n < source.length() && source.charAt(n) != '\n' && source.charAt(n) != '\r') n++;
                } else if (c == '/' && n + 1 < source.length() && source.charAt(n + 1) == '*') {
                    n += 2;
                    while (n + 1 < source.length() && !(source.charAt(n) == '*' && source.charAt(n + 1) == '/')) n++;
                    n = Math.min(source.length(), n + 2);
                } else if (identifierStart(c)) {
                    int start = n++;
                    while (n < source.length() && identifierPart(source.charAt(n))) n++;
                    result.add(new RawIdentifier(source.substring(start, n), new Range(key, start, n)));
                } else n++;
            }
            return List.copyOf(result);
        });
    }

    private void conflict(Path path, int offset, String message) {
        Conflict conflict = new Conflict(path, offset, message);
        if (!conflicts.contains(conflict)) conflicts.add(conflict);
    }

    private void checkpoint() {
        if (cancelled.getAsBoolean()) throw new CancellationException("Source refactoring was cancelled.");
    }

    private static Path normalize(Path path) { return Objects.requireNonNull(path, "path").toAbsolutePath().normalize(); }
    private static boolean isTranslationUnit(Path path) { return path.getFileName().toString().toLowerCase(java.util.Locale.ROOT).endsWith(".c"); }
    private static String withoutBom(String source) { return source.startsWith("﻿") ? " " + source.substring(1) : source; }
    private static boolean identifierStart(char c) { return c == '_' || c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z'; }
    private static boolean identifierPart(char c) { return identifierStart(c) || c >= '0' && c <= '9'; }
    private static boolean validName(String name) {
        if (name.isEmpty() || !identifierStart(name.charAt(0))) return false;
        for (int n = 1; n < name.length(); n++) if (!identifierPart(name.charAt(n))) return false;
        List<Token> tokens = new Lexer(name).tokenize();
        return tokens.size() == 2 && tokens.get(0).type == IDENTIFIER && !Set.of("bool", "auto", "register", "restrict", "goto", "inline", "_Bool", "_Atomic", "_Thread_local").contains(name);
    }

    private static int[] starts(String source) {
        List<Integer> starts = new ArrayList<>();
        starts.add(0);
        for (int n = 0; n < source.length(); n++) {
            char c = source.charAt(n);
            if (c == '\r') {
                if (n + 1 < source.length() && source.charAt(n + 1) == '\n') n++;
                starts.add(n + 1);
            } else if (c == '\n') starts.add(n + 1);
        }
        return starts.stream().mapToInt(Integer::intValue).toArray();
    }
}
