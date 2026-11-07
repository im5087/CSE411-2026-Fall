package sjc.type.checker;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.ArrayAccess;
import org.eclipse.jdt.core.dom.ArrayCreation;
import org.eclipse.jdt.core.dom.ArrayInitializer;
import org.eclipse.jdt.core.dom.Assignment;
import org.eclipse.jdt.core.dom.BooleanLiteral;
import org.eclipse.jdt.core.dom.ClassInstanceCreation;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.ConditionalExpression;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.ExpressionStatement;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.InfixExpression;
import org.eclipse.jdt.core.dom.IfStatement;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.core.dom.NullLiteral;
import org.eclipse.jdt.core.dom.NumberLiteral;
import org.eclipse.jdt.core.dom.ParenthesizedExpression;
import org.eclipse.jdt.core.dom.PostfixExpression;
import org.eclipse.jdt.core.dom.PrefixExpression;
import org.eclipse.jdt.core.dom.PrimitiveType;
import org.eclipse.jdt.core.dom.ReturnStatement;
import org.eclipse.jdt.core.dom.SimpleType;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.SimpleName;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;
import org.eclipse.jdt.core.dom.WhileStatement;

import sjc.annotation.NonNull;
import sjc.annotation.NonNullElements;
import sjc.annotation.ReadOnly;
import sjc.annotation.ReadOnlyElements;
import sjc.symboltable.SymbolTable;
import sjc.type.ArrayType;
import sjc.type.BaseType;
import sjc.type.ClassType;
import sjc.type.NonPrimitiveType;
import sjc.type.NullType;
import sjc.type.Type;
import sjc.type.TypeFactory;
import sjc.util.Pair;

/**
 * This class is used to type check a StaticJava {@link CompilationUnit} with a
 * given {@link SymbolTable}.
 *
 */
public class TypeChecker {
  public static class Error extends RuntimeException {
    private static final long serialVersionUID = 5322515711212690043L;
    public final @NonNull @ReadOnly ASTNode node;
    public Error(@NonNull final ASTNode node, @NonNull final String message) {
      super(message);
      this.node = node;
    }
  }

  /** Visitor for type checking an ExtendedStaticJava compilation unit. */
  protected static class Visitor extends ASTVisitor {
    protected Map<ASTNode, Object> symbolMap;
    public Map<ASTNode, Type> resultTypeMap = new HashMap<>();
    public Map<Object, Pair<Type, List<Type>>> resultMethodTypeMap =
        new HashMap<>();
    protected TypeFactory tf;
    protected ArrayType stringArrayType;
    protected String className;
    protected Type methodReturnType, resultingType;
    protected @NonNullElements
    @ReadOnlyElements
    Map<String, TypeDeclaration> classMap;
    protected @NonNullElements
    @ReadOnlyElements
    Map<Pair<String, String>, FieldDeclaration> fieldMap;
    protected Visitor(final TypeFactory tf, final SymbolTable st) {
      this.tf = tf;
      this.symbolMap = st.symbolMap;
      this.stringArrayType =
          tf.getArrayType(tf.getClassType("java.lang.String"));
      this.classMap = st.classMap;
      this.fieldMap = st.fieldMap;
      for (final Pair<String, String> p : st.fieldMap.keySet()) {
        final FieldDeclaration fd = st.fieldMap.get(p);
        final Type t = convertType(fd, fd.getType());
        final ClassType ct = tf.getClassType(p.first);
        ct.fieldTypeMap.put(p.second, t);
      }
    }
    protected Type getResult() {
      Type t = resultingType;
      resultingType = null;
      return t;
    }
    protected void setResult(Expression n, Type t) {
      resultTypeMap.put(n, t);
      resultingType = t;
    }
    protected Type convertType(ASTNode n, Class c) {
      if (c == void.class)
        return tf.Void;
      if (c == boolean.class)
        return tf.Boolean;
      if (c == int.class)
        return tf.Int;
      if (c == String[].class)
        return stringArrayType;
      if (!c.isArray())
        return tf.getClassType(c.getName());
      return tf.getArrayType((BaseType) convertType(n, c.getComponentType()));
    }
    protected Type convertType(ASTNode n, org.eclipse.jdt.core.dom.Type t) {
      if (t instanceof PrimitiveType) {
        PrimitiveType.Code c = ((PrimitiveType) t).getPrimitiveTypeCode();
        if (c == PrimitiveType.BOOLEAN)
          return tf.Boolean;
        if (c == PrimitiveType.INT)
          return tf.Int;
        if (c == PrimitiveType.VOID)
          return tf.Void;
      }
      if (t instanceof SimpleType) {
        String s = ((SimpleType) t).getName().getFullyQualifiedName();
        if (classMap.containsKey(s))
          return tf.getClassType(s);
        if ("String".equals(s) || "java.lang.String".equals(s))
          return stringArrayType.baseType;
      }
      if (t instanceof org.eclipse.jdt.core.dom.ArrayType)
        return tf.getArrayType((BaseType) convertType(
            n, ((org.eclipse.jdt.core.dom.ArrayType) t).getElementType()));
      throw new Error(n, "Unexpected Type: '" + t + "'");
    }
    protected void dispose() {
      symbolMap = null;
      resultTypeMap = null;
      resultMethodTypeMap = null;
      tf = null;
      stringArrayType = null;
      className = null;
      methodReturnType = resultingType = null;
      classMap = null;
      fieldMap = null;
    }
    protected Method resolveMethod(
        MethodInvocation n, String c, String m, Type[] a) {
      try {
        Class[] p = new Class[a.length];
        for (int i = 0; i < a.length; i++) p[i] = convertClass(n, a[i]);
        Method r = Class.forName(c).getMethod(m, p);
        symbolMap.put(n, r);
        return r;
      } catch (Exception e) {
        throw new Error(n, "Unresolvable method \"" + c + "." + m + "\"");
      }
    }
    protected Class convertClass(ASTNode n, Type t) {
      if (t == tf.Void)
        return void.class;
      if (t == tf.Boolean)
        return boolean.class;
      if (t == tf.Int)
        return int.class;
      if (t == stringArrayType)
        return String[].class;
      if (t instanceof ClassType)
        try {
          return Class.forName(((ClassType) t).name);
        } catch (Exception e) {
        }
      throw new Error(n, "Unresolvable Type: '" + t + "'");
    }
    protected void typeCheckMethodInvocation(
        MethodInvocation n, String c, String m, Type[] a, Method d) {
      if (a.length != d.getParameterTypes().length)
        throw new Error(n,
            "Wrong number of arguments to invoke method \"" + m + "\" in \"" + n
                + "\"");
      List<Type> p = new ArrayList<>();
      for (int i = 0; i < a.length; i++) {
        Type t = convertType(n, d.getParameterTypes()[i]);
        if (!((a[i] instanceof NullType) && (t instanceof NonPrimitiveType))
            && t != a[i])
          throw new Error(
              n, "Type mismatch the " + i + " argument in \"" + n + "\"");
        p.add(t);
      }
      Type r = convertType(n, d.getReturnType());
      if (!resultMethodTypeMap.containsKey(d))
        resultMethodTypeMap.put(d, new Pair<Type, List<Type>>(r, p));
      setResult(n, r);
    }
    protected void typeCheckMethodInvocation(
        MethodInvocation n, String c, String m, Type[] a, MethodDeclaration d) {
      if (a.length != d.parameters().size())
        throw new Error(n,
            "Wrong number of arguments to invoke method \"" + m + "\" in \"" + n
                + "\"");
      for (int i = 0; i < a.length; i++)
        if (!((a[i] instanceof NullType)
                && (convertType(n, ((SingleVariableDeclaration) d.parameters()
                    .get(i)).getType()) instanceof NonPrimitiveType))
            && convertType(n,
                ((SingleVariableDeclaration) d.parameters().get(i)).getType())
            != a[i])
          throw new Error(
              n, "Type mismatch the " + i + " argument in \"" + n + "\"");
      setResult(n, convertType(n, d.getReturnType2()));
    }
    protected Type evaluate(Expression expression) { //get type
      expression.accept(this);
      Type type = getResult();
      if (type == null)
        throw new Error(expression, "Missing expression type: '" + expression + "'");
      return type;
    }

    protected boolean isAssignable(Type target, Type source) { //대입 가능 여부
      return target != null && source != null
          && target != tf.Void && source != tf.Void
          && (target == source || (source == tf.Null && target instanceof NonPrimitiveType));
    }

    protected void checkCondition(ASTNode node, Expression expression, String kind) {//if, while, for의 조건식 검사
      if (evaluate(expression) != tf.Boolean)
        throw new Error(node,
            "Expecting a boolean type expression as the condition of a "
                + kind + "-statement: \"" + expression + "\"");
    }

    protected void checkOperand(InfixExpression node, Type actual, Type expected, String side) { //피연산자 검사
      if (actual != expected)
        throw new Error(node, "Expecting "
            + (expected == tf.Int ? "an int" : "a boolean")
            + " type expression as the " + side + "-hand operand of \""
            + node.getOperator() + "\" in \"" + node + "\"");
    }
    @Override
    public boolean visit(BooleanLiteral n) {
      setResult(n, tf.Boolean);
      return false;
    }
    @Override
    public boolean visit(NumberLiteral n) {
      setResult(n, tf.Int);
      return false;
    }
    @Override
    public boolean visit(ParenthesizedExpression n) {
      // TODO
      setResult(n, evaluate(n.getExpression()));
      return false;
    }
    @Override
    public boolean visit(FieldDeclaration n) {
      // TODO
      resultTypeMap.put(n, convertType(n, n.getType()));
      return false;
    }
    @Override
    public boolean visit(MethodDeclaration n) {
      // TODO
      Type previousReturnType = methodReturnType;
      Type returnType = convertType(n, n.getReturnType2());
      List<Type> parameterTypes = new ArrayList<>();
      for (Object item : n.parameters()) {
        SingleVariableDeclaration parameter = (SingleVariableDeclaration) item;
        Type parameterType = convertType(parameter, parameter.getType());
        parameterTypes.add(parameterType);
        resultTypeMap.put(parameter, parameterType);
      }
      resultMethodTypeMap.put(n, new Pair<Type, List<Type>>(returnType, parameterTypes));
      methodReturnType = returnType;
      try {
        if (n.getBody() != null) n.getBody().accept(this);
      } finally {
        methodReturnType = previousReturnType;
      }
      return false;
    }
    @Override
    public boolean visit(MethodInvocation n) {
      // TODO
      Type[] arguments = new Type[n.arguments().size()];
      for (int i = 0; i < arguments.length; i++)
        arguments[i] = evaluate((Expression) n.arguments().get(i));
      String owner = n.getExpression() == null
          ? className : n.getExpression().toString();
      String name = n.getName().getIdentifier();
      Object declaration = symbolMap.get(n);
      if (declaration instanceof MethodDeclaration) {
        typeCheckMethodInvocation(n, owner, name, arguments,
            (MethodDeclaration) declaration);
      } else {
        Method method = declaration instanceof Method ? (Method) declaration
            : resolveMethod(n, owner, name, arguments);
        typeCheckMethodInvocation(n, owner, name, arguments, method);
      }
      return false;
    }
    @Override
    public boolean visit(SimpleName n) {
      // TODO
      Object declaration = symbolMap.get(n);
      Type type;
      if (declaration instanceof FieldDeclaration) {
        type = convertType(n, ((FieldDeclaration) declaration).getType());
      } else if (declaration instanceof VariableDeclarationStatement) {
        type = convertType(n, ((VariableDeclarationStatement) declaration).getType());
      } else if (declaration instanceof SingleVariableDeclaration) {
        type = convertType(n, ((SingleVariableDeclaration) declaration).getType());
      } else {
        throw new Error(n, "Unresolvable variable: '" + n + "'");
      }
      setResult(n, type);
      return false;
    }
    @Override
    public boolean visit(TypeDeclaration n) {
      // TODO
      String previousClassName = className;
      className = n.getName().getIdentifier();
      resultTypeMap.put(n, tf.getClassType(className));
      try {
        for (FieldDeclaration field : n.getFields()) field.accept(this);
        for (MethodDeclaration method : n.getMethods()) method.accept(this);
      } finally {
        className = previousClassName;
      }
      return false;
    }
    @Override
    public boolean visit(VariableDeclarationStatement n) {
      // TODO
      resultTypeMap.put(n, convertType(n, n.getType()));
      return false;
    }
    @Override
    public boolean visit(Assignment n) {
      // TODO
      Type left = evaluate(n.getLeftHandSide());
      Type right = evaluate(n.getRightHandSide());
      if (!isAssignable(left, right))
        throw new Error(n,
            "Type mismatch in \"" + n + "\": " + left + " = " + right);
      return false;
    }
    @Override
    public boolean visit(ExpressionStatement n) {
      // TODO
      n.getExpression().accept(this);
      getResult();
      return false;
    }
    @Override
    public boolean visit(InfixExpression n) {
      // TODO
      Type left = evaluate(n.getLeftOperand());
      Type right = evaluate(n.getRightOperand());
      InfixExpression.Operator op = n.getOperator();
      if (op == InfixExpression.Operator.EQUALS
          || op == InfixExpression.Operator.NOT_EQUALS) {
        if (!isAssignable(left, right) && !isAssignable(right, left))
          throw new Error(n, "Type mismatch in \"" + n + "\": "
              + left + " " + op + " " + right);
        setResult(n, tf.Boolean);
      } else if (op == InfixExpression.Operator.CONDITIONAL_AND
          || op == InfixExpression.Operator.CONDITIONAL_OR) {
        checkOperand(n, left, tf.Boolean, "left");
        checkOperand(n, right, tf.Boolean, "right");
        setResult(n, tf.Boolean);
      } else if ((op == InfixExpression.Operator.AND
          || op == InfixExpression.Operator.OR
          || op == InfixExpression.Operator.XOR) && left == tf.Boolean) {
        checkOperand(n, right, tf.Boolean, "right");
        setResult(n, tf.Boolean);
      } else {
        checkOperand(n, left, tf.Int, "left");
        checkOperand(n, right, tf.Int, "right");
        boolean comparison = op == InfixExpression.Operator.LESS
            || op == InfixExpression.Operator.LESS_EQUALS
            || op == InfixExpression.Operator.GREATER
            || op == InfixExpression.Operator.GREATER_EQUALS;
        setResult(n, comparison ? tf.Boolean : tf.Int);
      }
      return false;
    }
    @Override
    public boolean visit(PrefixExpression n) {
      // TODO
      Type expected = n.getOperator() == PrefixExpression.Operator.NOT
          ? tf.Boolean : tf.Int;
      Type actual = evaluate(n.getOperand());
      if (actual != expected)
        throw new Error(n, "Expecting "
            + (expected == tf.Int ? "an int" : "a boolean")
            + " type expression as the operand of \"" + n.getOperator()
            + "\" in \"" + n + "\"");
      setResult(n, expected);
      return false;
    }
    @Override
    public boolean visit(ReturnStatement n) {
      // TODO
      if (methodReturnType == tf.Void) {
        if (n.getExpression() != null)
          throw new Error(n, "Unexpected return's expression in \"" + n + "\"");
      } else {
        if (n.getExpression() == null
            || !isAssignable(methodReturnType, evaluate(n.getExpression())))
          throw new Error(n,
              "Expecting " + methodReturnType + " return expression in \"" + n + "\"");
      }
      return false;
    }
    @Override
    public boolean visit(IfStatement n) {
      // TODO
      checkCondition(n, n.getExpression(), "if");
      n.getThenStatement().accept(this);
      if (n.getElseStatement() != null) n.getElseStatement().accept(this);
      return false;
    }
    @Override
    public boolean visit(WhileStatement n) {
      // TODO
      checkCondition(n, n.getExpression(), "while");
      n.getBody().accept(this);
      return false;
    }

    @Override
    public boolean visit(final ArrayAccess node) {
      // TODO
      Type array = evaluate(node.getArray());
      if (!(array instanceof ArrayType))
        throw new Error(node, "Expecting an array type in '" + node + "'");
      if (evaluate(node.getIndex()) != tf.Int)
        throw new Error(node, "Expecting an int type for the index of '" + node + "\"");
      setResult(node, ((ArrayType) array).baseType);
      return false;
    }

    @Override
    public boolean visit(final ArrayCreation node) {
      // TODO
      ArrayType arrayType = (ArrayType) convertType(node, node.getType());
      for (Object dimension : node.dimensions()) {
        if (evaluate((Expression) dimension) != tf.Int)
          throw new Error(node,
              "Expecting an int type expression for the array length in '" + node + "'");
      }
      ArrayInitializer initializer = node.getInitializer();
      if (initializer != null) {
        for (int i = 0; i < initializer.expressions().size(); i++) {
          Type element = evaluate((Expression) initializer.expressions().get(i));
          if (!isAssignable(arrayType.baseType, element))
            throw new Error(node, "Type mismatch in array initializer element "
                + i + " in '" + node + "': " + arrayType.baseType + " : " + element);
        }
      }
      setResult(node, arrayType);
      return false;
    }

    @Override
    public boolean visit(final ClassInstanceCreation node) {
      // TODO
      Type type = convertType(node, node.getType());
      if (!(type instanceof ClassType))
        throw new Error(node, "Expecting a class type in '" + node + "'");
      TypeDeclaration declaration = classMap.get(((ClassType) type).name);
      if (declaration == null)
        throw new Error(node, "Unexpected Type: '" + node.getType() + "'");
      symbolMap.put(node, declaration);
      setResult(node, type);
      return false;
    }

    @Override
    public boolean visit(final ConditionalExpression node) {
      // TODO
      if (evaluate(node.getExpression()) != tf.Boolean)
        throw new Error(node,
            "Expecting a boolean type expression as the condition in '" + node + "\"");
      Type thenType = evaluate(node.getThenExpression());
      Type elseType = evaluate(node.getElseExpression());
      Type type;
      if (isAssignable(thenType, elseType)) {
        type = thenType;
      } else if (isAssignable(elseType, thenType)) {
        type = elseType;
      } else {
        throw new Error(node, "Type mismatch for conditional expression '"
            + node + "\": " + thenType + " : " + elseType);
      }
      setResult(node, type);
      return false;
    }

    @Override
    public boolean visit(final DoStatement node) {
      // TODO
      node.getBody().accept(this);
      checkCondition(node, node.getExpression(), "while");
      return false;
    }

    @Override
    public boolean visit(final FieldAccess node) {
      // TODO
      Type owner = evaluate(node.getExpression());
      String name = node.getName().getIdentifier();
      if (!(owner instanceof ClassType))
        throw new Error(node, "Expecting a class type for field access '" + node + "'");
      FieldDeclaration declaration = fieldMap.get(new Pair<String, String>(
          ((ClassType) owner).name, name));
      if (declaration == null)
        throw new Error(node, "Unresolvable field: '" + node + "'");
      symbolMap.put(node, declaration);
      setResult(node, convertType(node, declaration.getType()));
      return false;
    }

    @Override
    public boolean visit(final ForStatement node) {
      // TODO
      for (Object initializer : node.initializers()) ((Expression) initializer).accept(this);
      if (node.getExpression() != null)
        checkCondition(node, node.getExpression(), "for");
      node.getBody().accept(this);
      for (Object updater : node.updaters()) ((Expression) updater).accept(this);
      getResult();
      return false;
    }

    @Override
    public boolean visit(final NullLiteral node) {
      // TODO
      setResult(node, tf.Null);
      return false;
    }

    @Override
    public boolean visit(final PostfixExpression node) {
      node.getOperand().accept(this);
      final Type t = getResult();
      if (t != this.tf.Int) {
        throw new Error(node,
            "Expecting an int type expression as the operand of \'"
                + node.getOperator() + "\': \"" + node.getOperand() + "\"");
      }
      // no need to set the type result for postfix expressions since
      // postfix expressions in StaticJava are statements,
      // i.e., they are evaluated for their side-effects.
      return false;
    }

  }

  /**
   * Type checks an ExtendedStaticJava {@link CompilationUnit} with the given
   * {@link SymbolTable} and the given {@link TypeFactory}. It also
   * resolves {@link MethodInvocation} of library call (and put its mapping in
   * the {@link SymbolTable}).
   * 
   * @param tf
   *          The {@link TypeFactory}.
   * @param cu
   *          The StaticJava {@link CompilationUnit}.
   * @param symbolTable
   *          The {@link SymbolTable} of the {@link CompilationUnit}
   * @return The {@link TypeTable}.
   * @throws Error
   *           If the type checker encounter type error in the
   *           {@link CompilationUnit}.
   */
  public static @NonNull
  TypeTable check(@NonNull final TypeFactory tf,
      @NonNull final CompilationUnit cu,
      @NonNull final SymbolTable symbolTable) throws Error {
    assert (tf != null) && (cu != null) && (symbolTable != null);

    final Visitor v = new Visitor(tf, symbolTable);
    cu.accept(v);
    final TypeTable result = new TypeTable(v.resultTypeMap,
        v.resultMethodTypeMap);
    v.dispose();
    return result;
  }

  /**
   * Declared as protected to disallow creation of this object outside from the
   * methods of this class.
   */
  protected TypeChecker() {
  }
}