package norswap.sigh.interpreter;

import norswap.sigh.ast.*;
import norswap.sigh.errors.ArrayLengthError;
import norswap.sigh.scopes.DeclarationKind;
import norswap.sigh.scopes.RootScope;
import norswap.sigh.scopes.Scope;
import norswap.sigh.scopes.SyntheticDeclarationNode;
import norswap.sigh.types.*;
import norswap.uranium.Reactor;
import norswap.utils.Util;
import norswap.utils.exceptions.Exceptions;
import norswap.utils.exceptions.NoStackException;
import norswap.utils.visitors.ValuedVisitor;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static norswap.utils.Util.cast;
import static norswap.utils.Vanilla.coIterate;
import static norswap.utils.Vanilla.map;

/**
 * Implements a simple but inefficient interpreter for Sigh.
 *
 * <h2>Limitations</h2>
 * <ul>
 *     <li>The compiled code currently doesn't support closures (using variables in functions that
 *     are declared in some surroudning scopes outside the function). The top scope is supported.
 *     </li>
 * </ul>
 *
 * <p>Runtime value representation:
 * <ul>
 *     <li>{@code Int}, {@code Float}, {@code Bool}: {@link Long}, {@link Double}, {@link Boolean}</li>
 *     <li>{@code String}: {@link String}</li>
 *     <li>{@code null}: {@link Null#INSTANCE}</li>
 *     <li>Arrays: {@code Object[]}</li>
 *     <li>Structs: {@code HashMap<String, Object>}</li>
 *     <li>Functions: the corresponding {@link DeclarationNode} ({@link FunDeclarationNode} or
 *     {@link SyntheticDeclarationNode}), excepted structure constructors, which are
 *     represented by {@link Constructor}</li>
 *     <li>Types: the corresponding {@link StructDeclarationNode}</li>
 * </ul>
 */
public final class Interpreter
{
    // ---------------------------------------------------------------------------------------------

    private final ValuedVisitor<SighNode, Object> visitor = new ValuedVisitor<>();
    private final Reactor reactor;
    private ScopeStorage storage = null;
    private RootScope rootScope;
    private ScopeStorage rootStorage;

    // ---------------------------------------------------------------------------------------------

    public Interpreter (Reactor reactor) {
        this.reactor = reactor;

        // expressions
        visitor.register(IntLiteralNode.class,           this::intLiteral);
        visitor.register(FloatLiteralNode.class,         this::floatLiteral);
        visitor.register(StringLiteralNode.class,        this::stringLiteral);
        visitor.register(ReferenceNode.class,            this::reference);
        visitor.register(ConstructorNode.class,          this::constructor);
        visitor.register(ArrayLiteralNode.class,         this::arrayLiteral);
        visitor.register(ParenthesizedNode.class,        this::parenthesized);
        visitor.register(FieldAccessNode.class,          this::fieldAccess);
        visitor.register(ArrayAccessNode.class,          this::arrayAccess);
        visitor.register(FunCallNode.class,              this::funCall);
        visitor.register(UnaryExpressionNode.class,      this::unaryExpression);
        visitor.register(BinaryExpressionNode.class,     this::binaryExpression);
        visitor.register(AssignmentNode.class,           this::assignment);

        // statement groups & declarations
        visitor.register(RootNode.class,                 this::root);
        visitor.register(BlockNode.class,                this::block);
        visitor.register(VarDeclarationNode.class,       this::varDecl);
        // no need to visitor other declarations! (use fallback)

        // statements
        visitor.register(ExpressionStatementNode.class,  this::expressionStmt);
        visitor.register(IfNode.class,                   this::ifStmt);
        visitor.register(WhileNode.class,                this::whileStmt);
        visitor.register(ReturnNode.class,               this::returnStmt);

        visitor.registerFallback(node -> null);
    }

    // ---------------------------------------------------------------------------------------------

    public Object interpret (SighNode root) {
        try {
            return run(root);
        } catch (PassthroughException e) {
            throw Exceptions.runtime(e.getCause());
        }
    }

    // ---------------------------------------------------------------------------------------------

    private Object run (SighNode node) {
        try {
            return visitor.apply(node);
        } catch (InterpreterException | Return | PassthroughException e) {
            throw e;
        } catch (RuntimeException e) {
            throw new InterpreterException("exception while executing " + node, e);
        }
    }

    // ---------------------------------------------------------------------------------------------

    /**
     * Used to implement the control flow of the return statement.
     */
    private static class Return extends NoStackException {
        final Object value;
        private Return (Object value) {
            this.value = value;
        }
    }

    // ---------------------------------------------------------------------------------------------

    private <T> T get(SighNode node) {
        return cast(run(node));
    }

    // ---------------------------------------------------------------------------------------------

    private Long intLiteral (IntLiteralNode node) {
        return node.value;
    }

    private Double floatLiteral (FloatLiteralNode node) {
        return node.value;
    }

    private String stringLiteral (StringLiteralNode node) {
        return node.value;
    }

    // ---------------------------------------------------------------------------------------------

    private Object parenthesized (ParenthesizedNode node) {
        return get(node.expression);
    }

    // ---------------------------------------------------------------------------------------------

    private Object[] arrayLiteral (ArrayLiteralNode node) {
        return map(node.components, new Object[0], visitor);
    }

    // ---------------------------------------------------------------------------------------------

    private Object binaryExpression (BinaryExpressionNode node)
    {
        Type leftType  = reactor.get(node.left, "type");
        Type rightType = reactor.get(node.right, "type");

        // Cases where both operands should not be evaluated.
        switch (node.operator) {
            case OR:  return booleanOp(node, false);
            case AND: return booleanOp(node, true);
        }

        Object left  = get(node.left);
        Object right = get(node.right);

        if (node.operator == BinaryOperator.ADD && !(leftType instanceof ArrayType)
                && (leftType instanceof StringType || rightType instanceof StringType))
            return convertToString(left) + convertToString(right);

        boolean floating = leftType instanceof FloatType || rightType instanceof FloatType;
        boolean numeric  = floating || leftType instanceof IntType;

        if (numeric)
            return numericOp(node, floating, (Number) left, (Number) right);

        else if((node.operator != BinaryOperator.DOLLAR) && (leftType instanceof ArrayType) && !(rightType instanceof ArrayType)){
            return recursiveMapOp(node, left, rightType);
        }

        switch (node.operator) {
            case EQUALITY:
                return  leftType.isPrimitive() ? left.equals(right) : left == right;
            case NOT_EQUALS:
                return  leftType.isPrimitive() ? !left.equals(right) : left != right;
        }
        //Array operation
        boolean IsArrayOperation = leftType instanceof ArrayType && rightType instanceof ArrayType;
        if (IsArrayOperation){
            Object [] result = new Object[((Object[]) left).length];
            arrayOp(node, (Object[]) left, (Object[]) right, result);
            return result;
        }

        //Map operation
        boolean isMap = leftType instanceof ArrayType && rightType instanceof FunType;
        if (isMap){
            return mapping(node, left, (FunDeclarationNode) right, ((FunType) rightType).paramTypes[0]);
        }


        throw new Error("should not reach here");
    }

    //----------------------------------------------------------------------------------------------
    //Map basic operators
    private Object recursiveMapOp(BinaryExpressionNode node, Object array, Type right){
        Object[] list = (Object[]) array;
        Object[] toReturn = new Object[list.length];

        if (list[0] instanceof Object[]) {
            for (int i = 0; i < list.length; i++)
                toReturn[i] = recursiveMapOp(node, list[i], right);
        } else {
            for (int i = 0; i < list.length; i++){
                boolean floating = list[i] instanceof Double || right instanceof FloatType;
                boolean numeric  = floating || list[i] instanceof Long;
                //If number in, call numericOp and store it in result
                if (numeric){
                    toReturn[i] = numericOp(node, floating, (Number) list[i], (Number) get(node.right));
                } else if (node.operator == BinaryOperator.ADD
                    && (list[i] instanceof String || right instanceof StringType)){
                    toReturn[i] = (String) (list[i]) + (String) (get(node.right));
                }
            }
        }
        return toReturn;
    }

    //Map operation

    private Object recursiveMap(BinaryExpressionNode node, Object array, FunDeclarationNode right, Type paramType){
        Object[] list = (Object[]) array;
        Object[] toReturn = new Object[list.length];
        if (list[0] instanceof Object[]){
            for (int i = 0; i < list.length; i++) toReturn[i] = recursiveMap(node, list[i], right, paramType);
        } else{
            for (int i = 0; i < list.length; i++) {
                //Check type of to create right funCall
                if (paramType instanceof IntType){
                    toReturn[i] = funCall(new FunCallNode(right.span, node.right, Arrays.asList(new IntLiteralNode[]{new IntLiteralNode(node.left.span, ((Long) list[i]).intValue())})));
                } else if (paramType instanceof StringType){
                    toReturn[i] = funCall(new FunCallNode(right.span, node.right, Arrays.asList(new StringLiteralNode[]{new StringLiteralNode(node.left.span, (String) list[i])})));
                } else if (paramType instanceof FloatType){
                    toReturn[i] = funCall(new FunCallNode(right.span, node.right, Arrays.asList(new FloatLiteralNode[]{new FloatLiteralNode(node.left.span, ((Double) list[i]).floatValue())})));
                } //Maybe check for BoolType
            }
        }
        return toReturn;
    }

    private Object mapping(BinaryExpressionNode node, Object left, FunDeclarationNode right, Type paramType){

        return recursiveMap(node, left, right, paramType);
    }



    // ---------------------------------------------------------------------------------------------
    //Need to sum Array Here
    private void arrayOp(BinaryExpressionNode node, Object[] left, Object[] right, Object[] result){
        //Check length and throw error if mismatch
        if (left.length != right.length || result.length != right.length) throw new PassthroughException(
            new ArrayLengthError("Trying to use operator on array/subarray of different length : Left is of length "
                + left.length + " and right of length " + right.length));

        for (int i = 0; i < left.length; i++){


            boolean floating = left[i] instanceof Double || right[i] instanceof Double;
            boolean numeric  = floating || left[i] instanceof Long;
            //If number in, call numericOp and store it in result
            if (numeric){
                result[i] = numericOp(node, floating, (Number) left[i], (Number) right[i]);
            }else if (node.operator == BinaryOperator.ADD
                && (left[i] instanceof String || right[i] instanceof String)){
                result[i] = (String) (left[i]) + (String) (right[i]);
            }
            //If contain an array type, reccursive called
            else if (left[i] instanceof Object[] && right[i] instanceof Object[]){
                Object[] subResult = new Object[((Object[]) left[i]).length];
                arrayOp(node, (Object[]) left[i], (Object[]) right[i], subResult);
                result[i] = subResult;
            } //Error if what is in the array of different type (Object[] and Long)
            else throw new PassthroughException(new Error("Trying to use operator on array of different type" +
                    "(Should never reach here and should have been detected in semanticAnalysis)"));
        }
    }





    // ---------------------------------------------------------------------------------------------

    private boolean booleanOp (BinaryExpressionNode node, boolean isAnd)
    {
        boolean left = get(node.left);
        return isAnd
                ? left && (boolean) get(node.right)
                : left || (boolean) get(node.right);
    }

    // ---------------------------------------------------------------------------------------------

    private Object numericOp
            (BinaryExpressionNode node, boolean floating, Number left, Number right)
    {
        long ileft, iright;
        double fleft, fright;

        if (floating) {
            fleft  = left.doubleValue();
            fright = right.doubleValue();
            ileft = iright = 0;
        } else {
            ileft  = left.longValue();
            iright = right.longValue();
            fleft = fright = 0;
        }

        Object result;
        if (floating)
            switch (node.operator) {
                case MULTIPLY:      return fleft *  fright;
                case DIVIDE:        return fleft /  fright;
                case REMAINDER:     return fleft %  fright;
                case ADD:           return fleft +  fright;
                case SUBTRACT:      return fleft -  fright;
                case GREATER:       return fleft >  fright;
                case LOWER:         return fleft <  fright;
                case GREATER_EQUAL: return fleft >= fright;
                case LOWER_EQUAL:   return fleft <= fright;
                case EQUALITY:      return fleft == fright;
                case NOT_EQUALS:    return fleft != fright;
                default:
                    throw new Error("should not reach here");
            }
        else
            switch (node.operator) {
                case MULTIPLY:      return ileft *  iright;
                case DIVIDE:        return ileft /  iright;
                case REMAINDER:     return ileft %  iright;
                case ADD:           return ileft +  iright;
                case SUBTRACT:      return ileft -  iright;
                case GREATER:       return ileft >  iright;
                case LOWER:         return ileft <  iright;
                case GREATER_EQUAL: return ileft >= iright;
                case LOWER_EQUAL:   return ileft <= iright;
                case EQUALITY:      return ileft == iright;
                case NOT_EQUALS:    return ileft != iright;
                default:
                    throw new Error("should not reach here");
            }
    }

    // ---------------------------------------------------------------------------------------------

    public Object assignment (AssignmentNode node)
    {
        if (node.left instanceof ReferenceNode) {
            Scope scope = reactor.get(node.left, "scope");
            String name = ((ReferenceNode) node.left).name;
            Object rvalue = get(node.right);
            assign(scope, name, rvalue, reactor.get(node, "type"));
            return rvalue;
        }

        if (node.left instanceof ArrayAccessNode) {
            ArrayAccessNode arrayAccess = (ArrayAccessNode) node.left;
            Object[] array = getNonNullArray(arrayAccess.array);
            int index = getIndex(arrayAccess.index);
            try {
                return array[index] = get(node.right);
            } catch (ArrayIndexOutOfBoundsException e) {
                throw new PassthroughException(e);
            }
        }

        if (node.left instanceof FieldAccessNode) {
            FieldAccessNode fieldAccess = (FieldAccessNode) node.left;
            Object object = get(fieldAccess.stem);
            if (object == Null.INSTANCE)
                throw new PassthroughException(
                    new NullPointerException("accessing field of null object"));
            Map<String, Object> struct = cast(object);
            Object right = get(node.right);
            struct.put(fieldAccess.fieldName, right);
            return right;
        }

        throw new Error("should not reach here");
    }

    // ---------------------------------------------------------------------------------------------

    private int getIndex (ExpressionNode node)
    {
        long index = get(node);
        if (index < 0)
            throw new ArrayIndexOutOfBoundsException("Negative index: " + index);
        if (index >= Integer.MAX_VALUE - 1)
            throw new ArrayIndexOutOfBoundsException("Index exceeds max array index (2ˆ31 - 2): " + index);
        return (int) index;
    }

    // ---------------------------------------------------------------------------------------------

    private Object[] getNonNullArray (ExpressionNode node)
    {
        Object object = get(node);
        if (object == Null.INSTANCE)
            throw new PassthroughException(new NullPointerException("indexing null array"));
        return (Object[]) object;
    }

    // ---------------------------------------------------------------------------------------------

    private Object unaryExpression (UnaryExpressionNode node)
    {
        // there is only NOT
        assert node.operator == UnaryOperator.NOT;
        return ! (boolean) get(node.operand);
    }

    // ---------------------------------------------------------------------------------------------

    private Object recursiveArrayAccess(ArrayAccessNode node, Object[] array, int depth){
        if (depth == 0){
            int arrayLength = array.length;
            IntLiteralNode start = (IntLiteralNode) ((ArraySelectionNode) node.index).start;
            IntLiteralNode end = (IntLiteralNode) ((ArraySelectionNode) node.index).end;
            long finalLength;
            if (start == null && end == null){
                return array;
            } else if (start == null){
                finalLength = end.value;
            } else if (end == null){
                finalLength = arrayLength - start.value;
            }else {
                finalLength = end.value - start.value;
            }
            Object[] returnArray = new Object[(int) finalLength];

            if (start == null){
                for (int i = 0; i < finalLength; i++) returnArray[i] = array[i];
            } else {
                for (int i = 0; i < finalLength; i++) returnArray[i] = array[i + (int) start.value];
            }
            return returnArray;
        } else{
            if (depth == 1){
                return recursiveArrayAccess(node, array, depth-1);
            }

            Object[] returnArray = new Object[array.length];
            for (int i = 0; i < array.length; i++) returnArray[i] = recursiveArrayAccess(node, (Object[]) array[i], depth-1);
            return returnArray;
        }
    }



    private Object arrayAccess (ArrayAccessNode node)
    {
        Object[] array = getNonNullArray(node.array);


        try {
            if (node.index instanceof ArraySelectionNode){
                int depth = 0;
                ArrayAccessNode iterNode = node;

                while (iterNode.array instanceof ArrayAccessNode){
                    iterNode = (ArrayAccessNode) iterNode.array;
                    depth++;
                }
                if (depth == 0) return recursiveArrayAccess(node, array, 0);

                Object[] returnArray = new Object[array.length];

                for (int i = 0; i < array.length; i++) returnArray[i] = recursiveArrayAccess(node, (Object[]) array[i], depth);

                return returnArray;

            }
            return array[getIndex(node.index)];
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new PassthroughException(e);
        }
    }

    // ---------------------------------------------------------------------------------------------

    private Object root (RootNode node)
    {
        assert storage == null;
        rootScope = reactor.get(node, "scope");
        storage = rootStorage = new ScopeStorage(rootScope, null);
        storage.initRoot(rootScope);

        try {
            node.statements.forEach(this::run);
        } catch (Return r) {
            return r.value;
            // allow returning from the main script
        } finally {
            storage = null;
        }
        return null;
    }

    // ---------------------------------------------------------------------------------------------

    private Void block (BlockNode node) {
        Scope scope = reactor.get(node, "scope");
        storage = new ScopeStorage(scope, storage);
        node.statements.forEach(this::run);
        storage = storage.parent;
        return null;
    }

    // ---------------------------------------------------------------------------------------------

    private Constructor constructor (ConstructorNode node) {
        // guaranteed safe by semantic analysis
        return new Constructor(get(node.ref));
    }

    // ---------------------------------------------------------------------------------------------

    private Object expressionStmt (ExpressionStatementNode node) {
        get(node.expression);
        return null;  // discard value
    }

    // ---------------------------------------------------------------------------------------------

    private Object fieldAccess (FieldAccessNode node)
    {
        Object stem = get(node.stem);
        if (stem == Null.INSTANCE)
            throw new PassthroughException(
                new NullPointerException("accessing field of null object"));
        return stem instanceof Map
                ? Util.<Map<String, Object>>cast(stem).get(node.fieldName)
                : (long) ((Object[]) stem).length; // only field on arrays
    }

    // ---------------------------------------------------------------------------------------------

    private Object funCall (FunCallNode node)
    {
        Object decl = get(node.function);
        node.arguments.forEach(this::run);
        Object[] args = map(node.arguments, new Object[0], visitor);

        if (decl == Null.INSTANCE)
            throw new PassthroughException(new NullPointerException("calling a null function"));

        if (decl instanceof SyntheticDeclarationNode)
            return builtin(((SyntheticDeclarationNode) decl).name(), args);

        if (decl instanceof Constructor)
            return buildStruct(((Constructor) decl).declaration, args);

        ScopeStorage oldStorage = storage;
        Scope scope = reactor.get(decl, "scope");
        storage = new ScopeStorage(scope, storage);

        FunDeclarationNode funDecl = (FunDeclarationNode) decl;
        coIterate(args, funDecl.parameters,
                (arg, param) -> storage.set(scope, param.name, arg));

        try {
            get(funDecl.block);
        } catch (Return r) {
            return r.value;
        } finally {
            storage = oldStorage;
        }
        return null;
    }

    // ---------------------------------------------------------------------------------------------

    private Object builtin (String name, Object[] args)
    {
        assert name.equals("print"); // only one at the moment
        String out = convertToString(args[0]);
        System.out.println(out);
        return out;
    }

    // ---------------------------------------------------------------------------------------------

    private String convertToString (Object arg)
    {
        if (arg == Null.INSTANCE)
            return "null";
        else if (arg instanceof Object[])
            return Arrays.deepToString((Object[]) arg);
        else if (arg instanceof FunDeclarationNode)
            return ((FunDeclarationNode) arg).name;
        else if (arg instanceof StructDeclarationNode)
            return ((StructDeclarationNode) arg).name;
        else if (arg instanceof Constructor)
            return "$" + ((Constructor) arg).declaration.name;
        else
            return arg.toString();
    }

    // ---------------------------------------------------------------------------------------------

    private HashMap<String, Object> buildStruct (StructDeclarationNode node, Object[] args)
    {
        HashMap<String, Object> struct = new HashMap<>();
        for (int i = 0; i < node.fields.size(); ++i)
            struct.put(node.fields.get(i).name, args[i]);
        return struct;
    }

    // ---------------------------------------------------------------------------------------------

    private Void ifStmt (IfNode node)
    {
        if (get(node.condition))
            get(node.trueStatement);
        else if (node.falseStatement != null)
            get(node.falseStatement);
        return null;
    }

    // ---------------------------------------------------------------------------------------------

    private Void whileStmt (WhileNode node)
    {
        while (get(node.condition))
            get(node.body);
        return null;
    }

    // ---------------------------------------------------------------------------------------------

    private Object reference (ReferenceNode node)
    {
        Scope scope = reactor.get(node, "scope");
        DeclarationNode decl = reactor.get(node, "decl");

        if (decl instanceof VarDeclarationNode
        || decl instanceof ParameterNode
        || decl instanceof SyntheticDeclarationNode
                && ((SyntheticDeclarationNode) decl).kind() == DeclarationKind.VARIABLE)
            return scope == rootScope
                ? rootStorage.get(scope, node.name)
                : storage.get(scope, node.name);

        return decl; // structure or function
    }

    // ---------------------------------------------------------------------------------------------

    private Void returnStmt (ReturnNode node) {
        throw new Return(node.expression == null ? null : get(node.expression));
    }

    // ---------------------------------------------------------------------------------------------

    private Void varDecl (VarDeclarationNode node)
    {
        Scope scope = reactor.get(node, "scope");
        assign(scope, node.name, get(node.initializer), reactor.get(node, "type"));
        return null;
    }

    // ---------------------------------------------------------------------------------------------

    private void assign (Scope scope, String name, Object value, Type targetType)
    {
        if (value instanceof Long && targetType instanceof FloatType)
            value = ((Long) value).doubleValue();
        storage.set(scope, name, value);
    }

    // ---------------------------------------------------------------------------------------------
}
