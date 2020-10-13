package singularityclasses;

import com.sun.source.tree.Tree;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;

import javax.lang.model.element.Modifier;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Traverses the AST and checks for each found class whether it conforms to the
 * singularity class requirements. If it does ...
 * 
 * @author Tim Scheurer
 */
public class Scanner extends JmlTreeScanner {

    private final static boolean VERBOSE = false;

    /**
     * Hack to check whether the return type of a method is primitive as we do not have a type-checked AST.
     */
    private static final List<String> primitiveTypes =
           Stream.of("int", "byte", "short", "float", "long", "double", "boolean", "char").collect(Collectors.toList());

    private final String FOOTPRINT = "footprint";

    /**
     * The JmlTypes instance for the current context.
     */
    private JmlTypes jmltypes;

    /**
     * The current context.
     */
    private Context context;

    /**
     * Current compilation unit.
     */
    private JmlTree.JmlCompilationUnit currentCompilationUnit;

    /**
     * Whether the currently visited compilation unit is a class or an interface.
     */
    private boolean currentCUIsClass;
    private boolean currentCUIsInterface;

    /**
     * Name of the class declared in the current compilation unit.
     */
    private String compUnitName;

    /**
     * The name of the implemented interface, if any.
     */
    private String interfaceName;

    /**
     * The currently visited method.
     */
    private JCTree.JCMethodDecl currentMethod;

    /**
     * The declaration for the current class/interface.
     */
    private JCTree.JCClassDecl currentClassDecl;

    /**
     * Whether the current class still has candidate status.
     * Set to false if we find a method that does not fulfill all requirements.
     */
    private boolean currentCUIsCandidate = true;

    /**
     * Whether we are looking at a class that does not implement an interface.
     */
    private boolean isClassButWrongImplements;

    /**
     * Whether we are looking at a class and extending something other than Object.
     */
    private boolean hasExtends;

    /**
     * Whether the current class has a newInstance method fulfilling the requirements.
     */
    private boolean hasNewInstance;

    /**
     * Whether the current method is the static newInstance method
     */
    private boolean currentMethodIsNewInstance;

    /**
     * Whether the currently visited method has a primitive return value.
     */
    private boolean methodHasPrimitiveReturn;

    /**
     * Whether the current method has void return type.
     */
    private boolean methodIsVoid;

    /**
     * Whether the currently visited compilation contains the required footprint field of type \locset.
     */
    private volatile boolean hasFootprintField;

    /**
     * Contains all the compilation units that contain interfaces that fulfill all of our requirement.
     * We then only have to find a class implementing this interface that also contains a newInstance method
     * fulfilling all requirements.
     */
    private Map<String, JmlTree.JmlCompilationUnit> foundCandidateInterfaces = new HashMap<>();

    /**
     * Contains all the compilation units that contain classes that contain a valid newInstance method and
     * implement a single interface and don't have an extends clause.
     */
    private Map<String, JmlTree.JmlCompilationUnit> foundCandidateClasses = new HashMap<>();

    /**
     * Contains all the compilation units that contain interfaces fulfilling all requirements for which
     * we also found matching classes implementing them.
     */
    private List<JmlTree.JmlCompilationUnit> foundValidInterfaces = new ArrayList<>();

    /***
     * Variables to help keep track of which requirements have been checked for the
     * current method and which are still missing or conflicting. Need to be reset
     * after each compilation unit.
     */
    private boolean methodEnsuresIso;
    private boolean methodEnsuresNewElemsFresh;
    private boolean methodAssignableFootprint;
    private boolean methodAccessibleFootprint;
    private boolean methodAssignableStrictlyNothing;

    /**
     * Flags to check for newInstance methods
     */
    private boolean newInstanceCorrectRetType;
    private boolean newInstanceEnsuresFreshResult;
    private boolean newInstanceEnsuresNewElems;
    private boolean newInstanceAssignableNothing;

    public Scanner(int mode, Context context) {
        super(mode);
        this.context = context;
        jmltypes = JmlTypes.instance(context);
    };

    //TODO: Make sure only references to Interfaces are used and there are no casts or direct constructor calls.
    //TODO: Maybe do that in a second pass?


    @Override
    public void scan(JCTree t) {
        super.scan(t);

        if (!(t instanceof JmlTree.JmlCompilationUnit)) return;

        // If we are in an interface having only good methods and the footprint field of correct type
        // add it to the candidates. If there already is a class candidate implementing this interface, then
        // also add it to the found valid interfaces.
        if (currentCUIsInterface && currentCUIsCandidate && hasFootprintField) {
            foundCandidateInterfaces.put(compUnitName, currentCompilationUnit);
            if (foundCandidateClasses.keySet().contains(compUnitName)) {
                foundValidInterfaces.add(currentCompilationUnit);
                System.out.println("Added \"" + compUnitName + "\" as valid interface");
            }
        }
        resetVars();
    }

    @Override
    public void visitClassDef(JCClassDecl that) {
        compUnitName = that.name.toString();
        currentClassDecl = that;

        if (that.getKind() == Tree.Kind.INTERFACE) {
            System.out.println("Visited Interface: " + compUnitName);
            currentCUIsInterface = true;
        } else if (that.getKind() == Tree.Kind.CLASS) {
            System.out.println("Visited Class: " + compUnitName);
            currentCUIsClass = true;
        }

        if (that.getExtendsClause() != null) {
            hasExtends = true;
            System.out.println("Found forbidden extends clause : \"" + that.getExtendsClause().toString() + "\"");
        }

        if (that.implementing.size() == 1) {
            interfaceName = that.implementing.head.toString();
            System.out.println("implementing the interface " + interfaceName);
        } else if (that.getKind() == Tree.Kind.CLASS){
            isClassButWrongImplements = true;
            System.out.println("\nMissing implemented interface or implementing too many interfaces");
        }

        // If we are in a class and the corresponding interface has already been found a candidate, then add the
        // interface to the valid ones.
        // If the interface has not been visited yet, add the current class to the class candidates.
        // We do not need more information about classes, so do not call super method and just return.
        if (currentCUIsClass && !hasExtends && !isClassButWrongImplements && currentClassDecl.getImplementsClause().head != null) {
            String implementedInterface = currentClassDecl.implementing.head.toString();
            if (foundCandidateInterfaces.keySet().contains(implementedInterface)) {
                foundValidInterfaces.add(foundCandidateInterfaces.get(implementedInterface));
                System.out.println("Added interface \"" + interfaceName + "\" as valid interface");
            } else {
                foundCandidateClasses.put(implementedInterface, currentCompilationUnit);
                System.out.println("Added class \"" + compUnitName + "\" as candidate class");
            }
            resetVars();
            return;
        }

        super.visitClassDef(that);
    }

    /*
     * Want to check if model variable footprint with type \locset exists.
     * Also check if it is an instance variable.
     *
     */
    @Override
    public void visitJmlVariableDecl(JmlTree.JmlVariableDecl that) {
        String fieldName = that.name.toString();
        JCTree.JCModifiers mods = that.mods;

        if (!fieldName.equals(FOOTPRINT)) return;

        boolean isInstance = false;
        boolean isModel = false;

        if (mods != null) {
            for (JCTree.JCAnnotation a : mods.annotations) {
                if (a.toString().contains(" instance ")) isInstance = true;
                if (a.toString().contains(" ghost ")) isModel = true;
            }
        }

        String type = that.vartype == null ? "" : that.vartype.toString();
        hasFootprintField = type.equals(jmltypes.LOCSET.toString()) && isModel && isInstance;
        if (hasFootprintField) System.out.println("Found instance ghost field \"footprint\" with type \\locset");

    super.visitJmlVariableDecl(that);
    }

    /*
     * Visit a JmlMethodDecl and check if the method fulfills all requirements.
     */
    @Override
    public void visitJmlMethodDecl(JmlTree.JmlMethodDecl that) {

        // We don't care about classes here
        if (currentCUIsClass) return;

        currentMethod = that;

        if (VERBOSE){
            System.out.println("Visited JmlTree.JmlMethodDecl: " + currentMethod.name);
        }

        String retType = that.getReturnType().toString();

        methodIsVoid = retType.equals("void");
        methodHasPrimitiveReturn = primitiveTypes.contains(retType);

        if (currentMethod.mods.getFlags().contains(Modifier.STATIC)) {
            if (currentCUIsClass) {
                System.out.println("Error: Found static method in class");
                currentCUIsCandidate = false;
            }

            if (currentCUIsInterface && !currentMethod.name.toString().equals("newInstance")) {
                currentCUIsCandidate = false;
                System.out.println("Error: Found static method not equal to newInstance");
                super.visitJmlMethodDecl(that);
                return;
            }
            if (!hasNewInstance) {
                System.out.println("\tFound newInstance method");
                currentMethodIsNewInstance = true;
                hasNewInstance = true;
            } else {
                System.out.println("Error: More than one newInstance method found.");
                currentMethodIsNewInstance = false;
            }

            if (retType.equals(compUnitName)) newInstanceCorrectRetType = true;
        }

        super.visitJmlMethodDecl(that);

        // Here we check whether the current method is good
        boolean currentMethodGood = (currentMethodIsNewInstance && newInstanceGood())
                                    || (!currentMethodIsNewInstance && currentMethodGood())
                                    || currentMethod.name.toString().equals("<init>");
        if (!currentMethodGood) {
            System.out.println("Found bad method with name \"" + currentMethod.name + "\"");
            currentCUIsCandidate = false;
        } else {
            System.out.println("Found good method with name \"" + currentMethod.name + "\"");
        }
        printPerMethodVars();
        resetPerMethodVars();
    }

    /*
     * Visit a JmlMethodClauseExpr, these include the keywords 'ensures' and 'requires', but not 'assignable or
     * 'accessible'.
     */
    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {

        // We don't care about classes here
        if (currentCUIsClass) return;

        String keyword = that.keyword;
        JCExpression expr = that.expression;

        if (VERBOSE) {
            System.out.print("Visited JmlMethodClauseExpr with keyword \"" + keyword + "\"");
            System.out.print(" with expression: \"" + expr + "\"\n");
        }

        if (keyword.equals("ensures")) {
            String expressionString = expr.toString();
            if (currentMethodIsNewInstance) {
                if (expressionString.equals("\\fresh(\\result)")) {
                    newInstanceEnsuresFreshResult = true;
                } else if (expressionString.equals("\\new_elems_fresh(\\result.footprint)")) {
                    newInstanceEnsuresNewElems = true;
                }
            } else {
                if (expressionString.equals("\\new_elems_fresh(footprint)")) {
                    methodEnsuresNewElemsFresh = true;
                } else if (!methodHasPrimitiveReturn && !methodIsVoid && expressionString.equals("\\dl_isolated_from(footprint, \\result)")) {
                    methodEnsuresIso = true;
                }
            }
        }
        super.visitJmlMethodClauseExpr(that);
    }

    /*
     * Visit a JmlMethodClauseStoreRef, this includes 'assignable' and 'accessible'.
     */
    @Override
    public void visitJmlMethodClauseStoreRef(JmlTree.JmlMethodClauseStoreRef that) {
        String keyword = that.keyword;
        List<JCExpression> exprs = that.list;

        if (VERBOSE) {
            System.out.print("Visited JmlMethodClauseStoreRef with keyword \"" + keyword + "\"");
        }

        if (exprs.size() != 1) {
            System.out.print("\n");
            return;
        }

        String expr = exprs.get(0).toString();
        if (VERBOSE) {
            System.out.print(" and expression: \"" + expr + "\"\n");
        }

        if (keyword.equals("assignable")) {
            if (expr.equals("footprint")) {
                methodAssignableFootprint = true;
            } else if (expr.equals("\\strictly_nothing")) {
                methodAssignableStrictlyNothing = true;
            } else if (expr.equals("\\nothing")) {
                newInstanceAssignableNothing = true;
            }
        } else if (keyword.equals("accessible") && expr.equals("footprint")) {
            methodAccessibleFootprint = true;
        }

        super.visitJmlMethodClauseStoreRef(that);
    }

    public void setCurrentCompilationUnit(JmlTree.JmlCompilationUnit cu) {
        currentCompilationUnit = cu;
    }

    public List<JmlTree.JmlCompilationUnit> getFoundValidInterfaces() {
        return foundValidInterfaces;
    }

    private void resetVars() {
        currentCUIsCandidate = true;
        hasNewInstance = false;
        isClassButWrongImplements = false;
        hasExtends = false;
        currentCUIsClass = false;
        currentCUIsInterface = false;
        hasFootprintField = false;
    }

    private void resetPerMethodVars() {
        methodEnsuresIso = false;
        methodEnsuresNewElemsFresh = false;
        methodAssignableFootprint = false;
        methodAccessibleFootprint = false;
        methodAssignableStrictlyNothing = false;

        newInstanceCorrectRetType = false;
        newInstanceAssignableNothing = false;
        newInstanceEnsuresFreshResult = false;
        newInstanceEnsuresNewElems = false;

        methodHasPrimitiveReturn = false;
        currentMethodIsNewInstance = false;
        methodIsVoid = false;
    }

    private void printPerMethodVars() {
        System.out.println("\tPrinting per method vars for method \"" + currentMethod.name +"\"");

        if (!currentMethodIsNewInstance) {
            System.out.println("\t------------ regular method flags -------------");

            System.out.println("\t\tmethodEnsuresIso " + methodEnsuresIso );
            System.out.println("\t\tmethodEnsuresNewElemsFresh " + methodEnsuresNewElemsFresh);
            System.out.println("\t\tmethodAssignableFootprint " + methodAssignableFootprint);
            System.out.println("\t\tmethodAccessibleFootprint " + methodAccessibleFootprint);
            System.out.println("\t\tmethodAssignableStrictlyNothing " + methodAssignableStrictlyNothing);
        }

        if (currentMethodIsNewInstance) {
            System.out.println("\t------------- newInstance flags --------------");

            System.out.println("\t\tnewInstanceCorrectRetType " + newInstanceCorrectRetType);
            System.out.println("\t\tnewInstanceAssignableNothing " + newInstanceAssignableNothing);
            System.out.println("\t\tnewInstanceFreshResult "+ newInstanceEnsuresFreshResult);
            System.out.println("\t\tnewInstanceEnsuresNewElems " + newInstanceEnsuresNewElems);
        }

        System.out.println("\t------------- general method flags ------------");

        System.out.println("\t\tmethodHasPrimitveReturn " + methodHasPrimitiveReturn);
        System.out.println("\t\tcurrentMethodIsNewInstance " + currentMethodIsNewInstance);
        System.out.println("\t\tmethodIsVoid " + methodIsVoid);
    }

    /*
     * Checks whether the current method fulfills either the requirements of a function or a procedure.
     * A function has
     *     - assignable \strictly_nothing;
     *     - accessible footprint;
     *     - ensures \isolated_from(footprint,\result);
     *     - a return value
     *
     * A procedure has
     *     - assignable footprint;
     *     - ensures \new_elems_fresh(footprint);
     *     - no return value
     */
    private boolean currentMethodGood() {
        boolean isFunc = methodAssignableStrictlyNothing &&
                methodAccessibleFootprint &&
                (methodHasPrimitiveReturn || methodIsVoid || methodEnsuresIso);
        boolean isProc = methodAssignableFootprint &&
                methodEnsuresNewElemsFresh &&
                methodIsVoid;

        return isFunc || isProc;
    }

    /*
     * Checks whether all flags for newInstance are set.
     */
    private boolean newInstanceGood() {
        return newInstanceEnsuresNewElems &&
                newInstanceEnsuresFreshResult &&
                newInstanceAssignableNothing &&
                newInstanceCorrectRetType;
    }
}