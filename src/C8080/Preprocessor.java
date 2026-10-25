package C8080;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.HashSet;
import java.util.concurrent.CancellationException;
import java.util.function.BooleanSupplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/** C preprocessor: macros, includes, conditionals, and line splicing, with maps back to physical source lines. */
public final class Preprocessor {
    private record Macro(List<String> parameters, String body, boolean variadic) {}
    private record Conditional(boolean parentEnabled, boolean branchTaken, boolean elseSeen) {}
    private record LogicalSource(String text, List<Integer> origins) {}
    private record MappedText(String text, int[] sourceStarts, int[] sourceEnds, boolean[] direct) {}
    /** Supplies normalized include paths; null means missing. Snapshot resolvers may serve unsaved files without disk access. */
    @FunctionalInterface
    public interface SourceResolver {
        /** Returns the include text, or null when this path is not available; throws IOException on a read failure. */
        String read(Path path) throws IOException;
    }
    private final SourceResolver sourceResolver;
    private final Map<Path, String> includeSources = new LinkedHashMap<>();
    private final List<boolean[]> directColumns = new ArrayList<>();

    /** Returns whether every generated character maps one-to-one, without macro expansion or line splicing. */
    public boolean isDirectLocation(int generatedLine, int generatedColumn, int generatedLength) {
        int line = generatedLine - 1;
        int start = generatedColumn - 1;
        if (line < 0 || line >= directColumns.size() || start < 0 || generatedLength < 1) return false;
        boolean[] direct = directColumns.get(line);
        if (generatedLength > direct.length - start) return false;
        for (int n = start; n < start + generatedLength; n++) if (!direct[n]) return false;
        return true;
    }
    /** Physical source location of a preprocessed span. */
    public record MappedLocation(SourceLine source, int column, int length) {}
    private static final class IncompleteMacro extends IllegalArgumentException {
        IncompleteMacro() { super("Unterminated macro argument list."); }
    }
    private final Map<String, Macro> macros = new LinkedHashMap<>();
    private final List<Path> includeDirectories;
    private final Deque<Path> includeStack = new ArrayDeque<>();
    private BooleanSupplier cancelled = () -> false;
    /** One physical source line with its file and 1-based line number. */
    public record SourceLine(Path path, int line, String text) {}
    private final List<SourceLine> sourceLines = new ArrayList<>();
    private final List<int[]> sourceColumnStarts = new ArrayList<>();
    private final List<int[]> sourceColumnEnds = new ArrayList<>();
    /** Returns an immutable source map for the most recent translation unit. */
    public List<SourceLine> sourceLines() {
        return List.copyOf(sourceLines);
    }

    /** Maps a generated token span to the original source span that produced it. */
    public MappedLocation mapLocation(int generatedLine, int generatedColumn, int generatedLength) {
        int lineIndex = generatedLine - 1;
        if (lineIndex < 0 || lineIndex >= sourceLines.size()) return null;
        SourceLine source = sourceLines.get(lineIndex);
        int[] starts = sourceColumnStarts.get(lineIndex);
        int[] ends = sourceColumnEnds.get(lineIndex);
        int start = Math.max(0, generatedColumn - 1);
        int finish = Math.min(starts.length, start + Math.max(1, generatedLength));
        if (start >= finish) return new MappedLocation(source, generatedColumn, Math.max(1, generatedLength));

        int mappedStart = Integer.MAX_VALUE;
        int mappedEnd = 0;
        for (int index = start; index < finish; index++) {
            mappedStart = Math.min(mappedStart, starts[index]);
            mappedEnd = Math.max(mappedEnd, ends[index]);
        }
        return new MappedLocation(source, mappedStart, Math.max(1, mappedEnd - mappedStart));
    }

    private final List<SourceLine> activeSourceLines = new ArrayList<>();

    /** Returns active physical lines, including active directives and included files. */
    public List<SourceLine> activeSourceLines() {
        return List.copyOf(activeSourceLines);
    }

    /** Expands a macro expression using the current translation unit's definitions. */
    public String expandForEditor(String text) {
        return expand(text, 0);
    }

    /** Returns the current macro names as an immutable snapshot. */
    public Set<String> definedMacroNames() {
        return Set.copyOf(macros.keySet());
    }

    /** Creates a preprocessor that resolves system headers from the bundled standard library. */
    public Preprocessor() {
        this(List.of());
    }

    /** Creates a preprocessor that also searches the given include directories. */
    public Preprocessor(List<Path> includeDirectories) {
        this(includeDirectories, path -> { SourceAccess.check(path); return Files.isRegularFile(path) ? SourceAccess.readString(path) : null; });
    }

    /** Creates a preprocessor using only the supplied include resolver, including for unsaved headers. */
    public Preprocessor(List<Path> includeDirectories, SourceResolver sourceResolver) {
        this.includeDirectories = List.copyOf(includeDirectories);
        this.sourceResolver = java.util.Objects.requireNonNull(sourceResolver, "sourceResolver");
    }

    /** Expands a source translation unit and resets macros and source maps for it. */
    public String process(String source) {
        return process(source, null);
    }

    /** Expands a source translation unit while preserving original file and line locations. */
    public String process(String source, Path sourcePath) {
        return process(source, sourcePath, () -> false);
    }

    /** Expands a translation unit and stops when the supplied cancellation state becomes true. */
    public String process(String source, Path sourcePath, BooleanSupplier cancellation) {
        BooleanSupplier previousCancellation = cancelled;
        cancelled = cancellation == null ? () -> false : cancellation;
        try {
            checkCancelled();
        sourceLines.clear();
        sourceColumnStarts.clear();
        sourceColumnEnds.clear();
        directColumns.clear();
        includeSources.clear();
        activeSourceLines.clear();
        macros.clear();
        String input = source == null ? "" : source;
        if (input.isEmpty()) {
            return "";
        }
        Path path = sourcePath == null ? null : sourcePath.toAbsolutePath().normalize();
        Path includeRoot = path != null && path.getParent() != null
                ? includeRootFor(path.getParent()) : Path.of("include").toAbsolutePath().normalize();
        try {
            return processText(input, path, includeRoot);
        } catch (IOException error) {
            throw new IllegalArgumentException("Preprocessor: " + error.getMessage(), error);
        }
        } finally {
            cancelled = previousCancellation;
        }
    }
    /** The nearest existing include/ directory at or above the translation unit's directory, so sources in
        nested module folders (src/VulcanOS/kernel/...) share their project's headers; otherwise the sibling include/. */
    public static Path includeRootFor(Path directory) {
        for (Path candidate = directory; candidate != null && SourceAccess.allows(candidate); candidate = candidate.getParent()) {
            Path include = candidate.resolve("include");
            if (Files.isDirectory(include)) return include;
        }
        return directory.resolve("include");
    }

    private String processText(String source, Path path, Path includeRoot) throws IOException {
        checkCancelled();
        if (path != null) {
            if (includeStack.size()>=64) throw new IllegalArgumentException("Include nesting exceeded 64 files: " + path);
            includeStack.push(path);
        }
        try {
            StringBuilder out = new StringBuilder(); Deque<Conditional> active = new ArrayDeque<>();
            boolean enabled = true;
            String[] physical = source.split("\\r\\n|\\r|\\n", -1);
            LogicalSource logical = spliceLines(physical);
            String[] lines = removeComments(logical.text()).split("\n", -1);
            for (int n = 0; n < lines.length; n++) {
                checkCancelled();
                int sourceIndex = logical.origins().get(n);
                String line = lines[n];
                String trim = line.trim();
                if (!trim.startsWith("#")) {
                    if (enabled) {
                        int first = n;
                        try {
                            while (n + 1 < lines.length && startsInvocationOnNextLine(line, lines[n + 1])) {
                                checkCancelled();
                                line += "\n" + lines[++n];
                            }
                            String expanded;
                            while (true) {
                                try { expanded = expand(line, 0); break; }
                                catch (IncompleteMacro incomplete) {
                                    if (n + 1 >= lines.length || lines[n + 1].stripLeading().startsWith("#")) throw incomplete;
                                    line += "\n" + lines[++n];
                                }
                            }
                            out.append(expanded).append('\n');
                            recordActive(path,physical,logical.origins(),first,n);
                            MappedText mapped = mapExpandedLine(line, expanded);
                            String[] expandedLines = expanded.split("\n", -1);
                            int mappedOffset = 0;
                            for (int offset = 0; offset < expandedLines.length; offset++) {
                                checkCancelled();
                                int original = logical.origins().get(Math.min(first + offset, n));
                                sourceLines.add(new SourceLine(path, original + 1, physical[original]));
                                int lineEnd = mappedOffset + expandedLines[offset].length();
                                if (mapped.sourceStarts().length == 0) {
                                    sourceColumnStarts.add(new int[0]);
                                    sourceColumnEnds.add(new int[0]);
                                    directColumns.add(new boolean[0]);
                                } else {
                                    sourceColumnStarts.add(java.util.Arrays.copyOfRange(
                                            mapped.sourceStarts(), mappedOffset, lineEnd));
                                    sourceColumnEnds.add(java.util.Arrays.copyOfRange(
                                            mapped.sourceEnds(), mappedOffset, lineEnd));
                                    boolean[] direct = java.util.Arrays.copyOfRange(mapped.direct(), mappedOffset, lineEnd);
                                    if (!line.equals(physical[sourceIndex]) && physical[sourceIndex].endsWith("\\"))
                                        java.util.Arrays.fill(direct, false);
                                    directColumns.add(direct);
                                }
                                mappedOffset = lineEnd + 1;
                            }
                        } catch (IllegalArgumentException error) {
                            throw new SourceDiagnostic(path, sourceIndex + 1, 1, Math.max(1, physical[sourceIndex].length()),
                                    physical[sourceIndex], error.getMessage() + "\nCheck the macro invocation and its arguments on this line.");
                        }
                    }
                    continue;
                }
                String directive = trim.substring(1).trim(); int split = -1;
                if(enabled)recordActive(path,physical,logical.origins(),n,n);
                for (int i = 0; i < directive.length(); i++) {if((i&255)==0)checkCancelled();if (Character.isWhitespace(directive.charAt(i))) { split = i; break; }}
                String name = split < 0 ? directive : directive.substring(0, split);
                String arg = split < 0 ? "" : directive.substring(split + 1).trim();
                try { switch (name) {
                    case "ifdef", "ifndef", "if" -> {
                        boolean parent = enabled;
                        boolean condition = parent && (name.equals("ifdef") ? macros.containsKey(arg) : name.equals("ifndef") ? !macros.containsKey(arg) : evalCondition(arg));
                        active.push(new Conditional(parent, condition, false)); enabled = condition;
                    }
                    case "elif" -> {
                        if (active.isEmpty()) throw diagnostic(path, sourceIndex, "#elif without #if");
                        Conditional previous = active.pop();
                        if (previous.elseSeen()) throw diagnostic(path, sourceIndex, "#elif after #else");
                        enabled = previous.parentEnabled() && !previous.branchTaken() && evalCondition(arg);
                        active.push(new Conditional(previous.parentEnabled(), previous.branchTaken() || enabled, false));
                    }
                    case "else" -> {
                        if (active.isEmpty()) throw diagnostic(path, sourceIndex, "#else without #if");
                        Conditional previous = active.pop();
                        if (previous.elseSeen()) throw diagnostic(path, sourceIndex, "Duplicate #else");
                        enabled = previous.parentEnabled() && !previous.branchTaken();
                        active.push(new Conditional(previous.parentEnabled(), true, true));
                    }
                    case "endif" -> { if (active.isEmpty()) throw diagnostic(path, sourceIndex, "#endif without #if"); enabled = active.pop().parentEnabled(); }
                    case "define" -> { if (enabled) define(arg, path, sourceIndex); }
                    case "undef" -> { if (enabled) macros.remove(arg); }
                    case "include" -> { if (enabled)out.append(includeText(expand(arg,0),path,includeRoot)); }
                    case "error" -> { if (enabled) throw diagnostic(path, sourceIndex, arg.isBlank() ? "#error" : arg); }
                    case "pragma", "line", "" -> { }
                    default -> { if(enabled)throw diagnostic(path, sourceIndex, "Unsupported directive #" + name); }
                }} catch(SourceDiagnostic error){throw error;}
                catch(IllegalArgumentException|IOException error){
                    throw new SourceDiagnostic(path,sourceIndex+1,Math.max(1,physical[sourceIndex].indexOf('#')+1),physical[sourceIndex].stripLeading().length(),physical[sourceIndex],error.getMessage()+"\nCheck this directive's include path, condition, or macro arguments.");
                }
            }
            if (!active.isEmpty()) throw new IllegalArgumentException("Unterminated conditional directive" + (path == null ? "" : " in " + path));
            return out.toString();
        } finally { if (path != null) includeStack.pop(); }
    }

    private void recordActive(Path path,String[] physical,List<Integer> origins,int first,int last){
        int start=origins.get(first),end=last+1<origins.size()?origins.get(last+1):physical.length;
        for(int n=start;n<end;n++){checkCancelled();activeSourceLines.add(new SourceLine(path,n+1,physical[n]));}
    }
    private void define(String text, Path path, int line) {
        Matcher m = Pattern.compile("^([A-Za-z_][A-Za-z_0-9]*)(?:\\(([^)]*)\\))?(?:\\s+(.*))?$").matcher(text);
        if (!m.matches()) throw diagnostic(path, line, "Invalid #define");
        List<String> params = null;
        boolean variadic=false;
        if (m.group(2) != null) {
            params = new ArrayList<>();
            if (!m.group(2).isBlank()) for (String p : m.group(2).split(",",-1)) {
                p=p.trim();if(p.equals("...")){p="__VA_ARGS__";variadic=true;}
                else if(variadic||!p.matches("[A-Za-z_][A-Za-z_0-9]*"))throw diagnostic(path,line,"Invalid macro parameter.");
                if(params.contains(p))throw diagnostic(path,line,"Duplicate macro parameter "+p);params.add(p);
            }
        }
        macros.put(m.group(1), new Macro(params, m.group(3) == null ? "" : m.group(3),variadic));
    }

    private String expand(String text, int depth) {
        return expand(text,depth,Set.of());
    }

    /** Maps expanded characters to the source token or macro invocation that produced them. */
    private MappedText mapExpandedLine(String input, String expanded) {
        if (input.indexOf('\n') >= 0 || expanded.indexOf('\n') >= 0)
            return new MappedText(expanded, new int[0], new int[0], new boolean[0]);

        int[] starts = new int[expanded.length()];
        int[] ends = new int[expanded.length()];
        boolean[] direct = new boolean[expanded.length()];
        int sourceIndex = 0;
        int expandedIndex = 0;

        while (sourceIndex < input.length() && expandedIndex < expanded.length()) {
            if((expandedIndex&255)==0)checkCancelled();
            char current = input.charAt(sourceIndex);
            if (Character.isLetter(current) || current == '_') {
                int identifierEnd = sourceIndex + 1;
            while (identifierEnd < input.length()
                    && (Character.isLetterOrDigit(input.charAt(identifierEnd)) || input.charAt(identifierEnd) == '_')) {
                if((identifierEnd&255)==0)checkCancelled();
                    identifierEnd++;
            }
                String name = input.substring(sourceIndex, identifierEnd);
                Macro macro = macros.get(name);
                int invocationEnd = identifierEnd;
                if (macro != null && macro.parameters() != null) {
                    int open = invocationEnd;
                    while (open < input.length() && Character.isWhitespace(input.charAt(open))) {if((open&255)==0)checkCancelled();open++;}
                    if (open < input.length() && input.charAt(open) == '(')
                        invocationEnd = matchingParen(input, open) + 1;
                    else macro = null;
                }
                if (macro != null) {
                    String replacement = expand(input.substring(sourceIndex, invocationEnd), 0);
                    if (!replacement.isEmpty() && expanded.startsWith(replacement, expandedIndex)) {
                        int sourceStart = sourceIndex + 1;
                        int sourceEnd = invocationEnd + 1;
                        for (int i = 0; i < replacement.length(); i++) {
                            if((i&255)==0)checkCancelled();
                            starts[expandedIndex + i] = sourceStart;
                            ends[expandedIndex + i] = sourceEnd;
                        }
                        sourceIndex = invocationEnd;
                        expandedIndex += replacement.length();
                        continue;
                    }
                }
            }

            if (expanded.charAt(expandedIndex) == current) {
                starts[expandedIndex] = sourceIndex + 1;
                ends[expandedIndex] = sourceIndex + 2;
                direct[expandedIndex] = true;
                sourceIndex++;
                expandedIndex++;
            } else {
                starts[expandedIndex] = sourceIndex + 1;
                ends[expandedIndex] = Math.min(input.length() + 1, sourceIndex + 2);
                expandedIndex++;
            }
        }
        while (expandedIndex < expanded.length()) {
            if((expandedIndex&255)==0)checkCancelled();
            starts[expandedIndex] = Math.max(1, input.length());
            ends[expandedIndex] = Math.max(2, input.length() + 1);
            expandedIndex++;
        }
        return new MappedText(expanded, starts, ends, direct);
    }

    private String expand(String text, int depth,Set<String> disabled) {
        if (depth > 32) throw new IllegalArgumentException("Macro expansion exceeded 32 levels.");
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < text.length();) {
            if((i&255)==0)checkCancelled();
            char c = text.charAt(i);
            if (c == '"' || c == '\'') { char q = c; int start = i++; while (i < text.length()) {if((i&255)==0)checkCancelled();if (text.charAt(i++) == '\\' && i < text.length()) i++; else if (text.charAt(i - 1) == q) break; } out.append(text, start, i); continue; }
            if (Character.isLetter(c) || c == '_') {
                int start = i++; while (i < text.length() && (Character.isLetterOrDigit(text.charAt(i)) || text.charAt(i) == '_')) {if((i&255)==0)checkCancelled();i++;}
                String name = text.substring(start, i); Macro macro = macros.get(name);
                if (macro == null || disabled.contains(name)) { out.append(name); continue; }
                String replacement = macro.body;
                if (macro.parameters != null) {
                    int open = i; while (open < text.length() && Character.isWhitespace(text.charAt(open))) {if((open&255)==0)checkCancelled();open++;}
                    if (open >= text.length() || text.charAt(open) != '(') { out.append(name); continue; }
                    int close = matchingParen(text, open); List<String> args = splitArguments(text.substring(open + 1, close));
                    int fixed=macro.parameters.size()-(macro.variadic?1:0);
                    if(args.isEmpty()&&fixed==1)args=new ArrayList<>(List.of(""));
                    if (macro.variadic?args.size()<fixed:args.size()!=fixed) throw new IllegalArgumentException("Macro " + name + " expects " + fixed + " fixed argument(s).");
                    Map<String,String> raw=new LinkedHashMap<>(),expanded=new LinkedHashMap<>();
                    for(int p=0;p<fixed;p++){checkCancelled();raw.put(macro.parameters.get(p),args.get(p));expanded.put(macro.parameters.get(p),expand(args.get(p),depth+1,disabled));}
                    if(macro.variadic){String rest=String.join(",",args.subList(fixed,args.size()));raw.put("__VA_ARGS__",rest);expanded.put("__VA_ARGS__",expand(rest,depth+1,disabled));}
                    replacement=substitute(replacement,raw,expanded);
                    i = close + 1;
                }
                Set<String> nested=new HashSet<>(disabled);nested.add(name);

                String alias=replacement.trim();Macro aliasMacro=macros.get(alias);
                int open=i;while(open<text.length()&&Character.isWhitespace(text.charAt(open)))open++;
                if(macro.parameters==null&&aliasMacro!=null&&aliasMacro.parameters!=null&&open<text.length()&&text.charAt(open)=='('){int close=matchingParen(text,open);replacement+=text.substring(i,close+1);i=close+1;}
                out.append(expand(replacement, depth + 1,nested)); continue;
            }
            out.append(c); i++;
        }
        return out.toString();
    }
    private static final Pattern PP_TOKEN=Pattern.compile("\\s+|\"(?:\\\\.|[^\"\\\\])*\"|'(?:\\\\.|[^'\\\\])*'|[A-Za-z_][A-Za-z_0-9]*|(?:[0-9]|\\.[0-9])(?:[eEpP][+-]|[A-Za-z_0-9.])*|##|<<=|>>=|\\.\\.\\.|==|!=|<=|>=|&&|\\|\\||\\+\\+|--|->|<<|>>|[+*/%&|^!-]=|.");
    private String substitute(String source,Map<String,String> raw,Map<String,String> expanded){
        List<String> tokens=new ArrayList<>();Matcher matcher=PP_TOKEN.matcher(source);while(matcher.find()){checkCancelled();if(!matcher.group().isBlank())tokens.add(matcher.group());}
        List<String> output=new ArrayList<>();
        for(int n=0;n<tokens.size();n++){
            checkCancelled();
            String token=tokens.get(n);
            if(token.equals("#")&&n+1<tokens.size()&&raw.containsKey(tokens.get(n+1))){String value=raw.get(tokens.get(++n)).trim().replaceAll("\\s+"," ");output.add("\""+value.replace("\\","\\\\").replace("\"","\\\"")+"\"");}
            else if(token.equals("##")){
                if(output.isEmpty()||n+1>=tokens.size())throw new IllegalArgumentException("Token paste requires two operands.");
                String right=tokens.get(++n);String left=output.remove(output.size()-1);String pasted=left+raw.getOrDefault(right,right);
                if(!pasted.isEmpty()){
                    Matcher pastedToken=PP_TOKEN.matcher(pasted);
                    if(!pastedToken.lookingAt()||pastedToken.end()!=pasted.length())throw new IllegalArgumentException("Token paste must produce one preprocessing token.");
                }
                output.add(pasted);
            }else output.add((n+1<tokens.size()&&tokens.get(n+1).equals("##")?raw:expanded).getOrDefault(token,token));
        }
        return String.join(" ",output);
    }
    private String removeComments(String source){
        StringBuilder out=new StringBuilder();char quote=0;
        for(int n=0;n<source.length();n++){
            if((n&255)==0)checkCancelled();
            char c=source.charAt(n);
            if(quote!=0){out.append(c);if(c=='\\'&&n+1<source.length())out.append(source.charAt(++n));else if(c==quote)quote=0;}
            else if(c=='\"'||c=='\''){quote=c;out.append(c);}
            else if(c=='/'&&n+1<source.length()&&source.charAt(n+1)=='/') {out.append("  " );n++;while(n+1<source.length()&&source.charAt(n+1)!='\n'){if((n&255)==0)checkCancelled();n++;out.append(' ');}}
            else if(c=='/'&&n+1<source.length()&&source.charAt(n+1)=='*'){
                out.append("  " );n+=2;while(n<source.length()&&!(source.charAt(n)=='*'&&n+1<source.length()&&source.charAt(n+1)=='/')){if((n&255)==0)checkCancelled();out.append(source.charAt(n)=='\n'?'\n':' ');n++;}
                if(n>=source.length())throw new IllegalArgumentException("Unterminated preprocessing comment.");out.append("  ");n++;
            }else out.append(c);
        }
        return out.toString();
    }
    /**
     * Returns the matching closing parenthesis while ignoring delimiters inside quoted literals.
     * @param source text containing the parenthesized expression
     * @param openingIndex index of the opening parenthesis
     * @return index of the matching closing parenthesis
     * @throws IllegalArgumentException if openingIndex is invalid or no matching parenthesis exists
     */
    public static int matchingParenthesis(String source, int openingIndex) {
        if (source == null || openingIndex < 0 || openingIndex >= source.length()
                || source.charAt(openingIndex) != '(') {
            throw new IllegalArgumentException("Opening index must point to a parenthesis.");
        }
        return matchingParen(source, openingIndex, () -> {});
    }

    private int matchingParen(String s, int open) {
        return matchingParen(s, open, this::checkCancelled);
    }

    private static int matchingParen(String s, int open, Runnable checkpoint) {
        int depth = 0; char quote = 0;
        for (int i = open; i < s.length(); i++) {
            if((i&255)==0)checkpoint.run();
            char c = s.charAt(i);
            if (quote != 0) {
                if (c == '\\') i++;
                else if (c == quote) quote = 0;
                continue;
            }
            if (c == '"' || c == '\'') quote = c;
            else if (c == '(') depth++;
            else if (c == ')' && --depth == 0) return i;
        }
        throw new IncompleteMacro();
    }
    private List<String> splitArguments(String value) {
        List<String> args = new ArrayList<>(); if (value.isBlank()) return args;
        int depth = 0, from = 0; char quote = 0;
        for (int i = 0; i < value.length(); i++) {
            if((i&255)==0)checkCancelled();
            char c = value.charAt(i);
            if (quote != 0) {
                if (c == '\\') i++;
                else if (c == quote) quote = 0;
            } else if (c == '"' || c == '\'') quote = c;
            else if (c == '(') depth++;
            else if (c == ')') depth--;
            else if (c == ',' && depth == 0) { args.add(value.substring(from, i).trim()); from = i + 1; }
        }
        args.add(value.substring(from).trim()); return args;
    }

    private LogicalSource spliceLines(String[] physical) {
        StringBuilder text = new StringBuilder();
        List<Integer> origins = new ArrayList<>();
        for (int n = 0; n < physical.length; n++) {
            checkCancelled();
            origins.add(n);
            String line = physical[n];
            while (line.endsWith("\\") && n + 1 < physical.length) {
                checkCancelled();
                line = line.substring(0, line.length() - 1) + physical[++n];
            }
            if (!origins.isEmpty() && origins.size() > 1) text.append('\n');
            text.append(line);
        }
        return new LogicalSource(text.toString(), List.copyOf(origins));
    }

    private boolean startsInvocationOnNextLine(String line, String following) {
        if (!following.stripLeading().startsWith("(")) return false;
        Matcher last = Pattern.compile("([A-Za-z_][A-Za-z_0-9]*)\\s*$").matcher(line);
        if (!last.find()) return false;
        Macro macro = macros.get(last.group(1));
        if (macro != null && macro.parameters() == null) macro = macros.get(macro.body().trim());
        return macro != null && macro.parameters() != null;
    }
    private Path findInclude(String arg, Path including, Path includeRoot) throws IOException {
        boolean quoted = arg.startsWith("\"") && arg.endsWith("\""); boolean system = arg.startsWith("<") && arg.endsWith(">");
        if (!quoted && !system) throw new IllegalArgumentException("Invalid #include: " + arg);
        String name = arg.substring(1, arg.length() - 1); List<Path> candidates = new ArrayList<>();
        if(Path.of(name).isAbsolute())candidates.add(Path.of(name));
        if (quoted && including != null && including.getParent() != null) candidates.add(including.getParent().resolve(name));
        else if(quoted)candidates.add(Path.of(name));
        for (Path dir : includeDirectories) candidates.add(dir.resolve(name));
        candidates.add(includeRoot.resolve(name));
        if (system) candidates.add(Path.of("src", "stdlib", "include").resolve(name));
        for (Path candidate : candidates) {
            checkCancelled();
            Path normalized = candidate.toAbsolutePath().normalize();
            String contents = includeSources.get(normalized);
            if (contents == null) contents = sourceResolver.read(normalized);
            if (contents != null) {
                includeSources.put(normalized, contents);
                return normalized;
            }
        }
        throw new IllegalArgumentException("Include file not found: " + name);
    }
    private String includeText(String arg,Path path,Path includeRoot)throws IOException{
        checkCancelled();
        try{Path include=findInclude(arg,path,includeRoot);String contents=includeSources.get(include);checkCancelled();return processText(contents,include,includeRoot);}
        catch(IllegalArgumentException missing){
            if(!missing.getMessage().startsWith("Include file not found:")||!arg.startsWith("<")||!arg.endsWith(">"))throw missing;
            String name=arg.substring(1,arg.length()-1);
            if(name.contains("..")||name.startsWith("/"))throw missing;
            try(var resource=Preprocessor.class.getResourceAsStream("/stdlib/include/"+name)){
                if(resource==null)throw missing;byte[] contents=resource.readAllBytes();checkCancelled();return processText(new String(contents,java.nio.charset.StandardCharsets.UTF_8),Path.of("src","stdlib","include",name).toAbsolutePath(),includeRoot);
            }
        }
    }

    private void checkCancelled(){if(cancelled.getAsBoolean())throw new CancellationException("Preprocessing was cancelled.");}
    private boolean evalCondition(String expression) {
        Matcher defined = Pattern.compile("defined\\s*(?:\\(\\s*([A-Za-z_][A-Za-z_0-9]*)\\s*\\)|([A-Za-z_][A-Za-z_0-9]*))").matcher(expression);
        StringBuffer normalized = new StringBuffer();
        while (defined.find()) { checkCancelled();String id = defined.group(1) == null ? defined.group(2) : defined.group(1); defined.appendReplacement(normalized, macros.containsKey(id) ? "1" : "0"); }
        defined.appendTail(normalized);
        StringBuilder condition=new StringBuilder();Matcher token=PP_TOKEN.matcher(expand(normalized.toString(),0));
        while(token.find()){checkCancelled();String value=token.group();condition.append(value.matches("[A-Za-z_][A-Za-z_0-9]*")?"0":value);}
        String expanded=condition.toString();
        try { return Parser.parseIntegerConstantExpression(expanded, cancelled).signum() != 0; }
        catch (CancellationException cancelled) { throw cancelled; }
        catch (RuntimeException error) { throw new IllegalArgumentException("Invalid #if expression '" + expression + "': " + error.getMessage(), error); }
    }
    private static IllegalArgumentException diagnostic(Path path, int line, String message) { return new IllegalArgumentException((path == null ? "<source>" : path.toString()) + ":" + (line + 1) + ": " + message); }
}
