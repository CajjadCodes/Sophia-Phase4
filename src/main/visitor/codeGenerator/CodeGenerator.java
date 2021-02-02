package main.visitor.codeGenerator;

import main.ast.nodes.Program;
import main.ast.nodes.declaration.classDec.ClassDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.ConstructorDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.FieldDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.MethodDeclaration;
import main.ast.nodes.declaration.variableDec.VarDeclaration;
import main.ast.nodes.expression.*;
import main.ast.nodes.expression.operators.BinaryOperator;
import main.ast.nodes.expression.operators.UnaryOperator;
import main.ast.nodes.expression.values.ListValue;
import main.ast.nodes.expression.values.NullValue;
import main.ast.nodes.expression.values.primitive.BoolValue;
import main.ast.nodes.expression.values.primitive.IntValue;
import main.ast.nodes.expression.values.primitive.StringValue;
import main.ast.nodes.statement.*;
import main.ast.nodes.statement.loop.BreakStmt;
import main.ast.nodes.statement.loop.ContinueStmt;
import main.ast.nodes.statement.loop.ForStmt;
import main.ast.nodes.statement.loop.ForeachStmt;
import main.ast.types.NullType;
import main.ast.types.Type;
import main.ast.types.functionPointer.FptrType;
import main.ast.types.list.ListNameType;
import main.ast.types.list.ListType;
import main.ast.types.single.BoolType;
import main.ast.types.single.ClassType;
import main.ast.types.single.IntType;
import main.ast.types.single.StringType;
import main.symbolTable.SymbolTable;
import main.symbolTable.exceptions.ItemNotFoundException;
import main.symbolTable.items.ClassSymbolTableItem;
import main.symbolTable.items.FieldSymbolTableItem;
import main.symbolTable.items.LocalVariableSymbolTableItem;
import main.symbolTable.items.MethodSymbolTableItem;
import main.symbolTable.utils.graph.Graph;
import main.visitor.Visitor;
import main.visitor.typeChecker.ExpressionTypeChecker;

import java.io.*;
import java.lang.annotation.ElementType;
import java.util.ArrayList;
import java.util.List;

public class CodeGenerator extends Visitor<String> {
    ExpressionTypeChecker expressionTypeChecker;
    Graph<String> classHierarchy;
    private String outputPath;
    private FileWriter currentFile;
    private ClassDeclaration currentClass;
    private MethodDeclaration currentMethod;

    private int labelCounter;
    private ArrayList<ArrayList<String>> labelsStack;

    private ArrayList<String> currentSlots;
    private int tempVarNumber;

    public CodeGenerator(Graph<String> classHierarchy) {
        this.classHierarchy = classHierarchy;
        this.expressionTypeChecker = new ExpressionTypeChecker(classHierarchy);
        this.labelsStack = new ArrayList<>();
        this.currentSlots = new ArrayList<>();
        this.prepareOutputFolder();
    }

    private void prepareOutputFolder() {
        this.outputPath = "output/";
        String jasminPath = "utilities/jarFiles/jasmin.jar";
        String listClassPath = "utilities/codeGenerationUtilityClasses/List.j";
        String fptrClassPath = "utilities/codeGenerationUtilityClasses/Fptr.j";
        try{
            File directory = new File(this.outputPath);
            File[] files = directory.listFiles();
            if(files != null)
                for (File file : files)
                    file.delete();
            directory.mkdir();
        }
        catch(SecurityException e) { }
        copyFile(jasminPath, this.outputPath + "jasmin.jar");
        copyFile(listClassPath, this.outputPath + "List.j");
        copyFile(fptrClassPath, this.outputPath + "Fptr.j");
    }

    private void copyFile(String toBeCopied, String toBePasted) {
        try {
            File readingFile = new File(toBeCopied);
            File writingFile = new File(toBePasted);
            InputStream readingFileStream = new FileInputStream(readingFile);
            OutputStream writingFileStream = new FileOutputStream(writingFile);
            byte[] buffer = new byte[1024];
            int readLength;
            while ((readLength = readingFileStream.read(buffer)) > 0)
                writingFileStream.write(buffer, 0, readLength);
            readingFileStream.close();
            writingFileStream.close();
        } catch (IOException e) { }
    }

    private void createFile(String name) {
        try {
            String path = this.outputPath + name + ".j";
            File file = new File(path);
            file.createNewFile();
            FileWriter fileWriter = new FileWriter(path);
            this.currentFile = fileWriter;
        } catch (IOException e) {}
    }

    private void addCommand(String command) {
        try {
            command = String.join("\n\t\t", command.split("\n"));
            if(command.startsWith("Label_"))
                this.currentFile.write("\t" + command + "\n");
            else if(command.startsWith("."))
                this.currentFile.write(command + "\n");
            else
                this.currentFile.write("\t\t" + command + "\n");
            this.currentFile.flush();
        } catch (IOException e) {}
    }

    private void addBlankLine() {
        try {
            this.currentFile.write("\n");
            this.currentFile.flush();
        } catch (IOException ignored) {}
    }

    private void pushLabels(String nAfter, String nBrk, String nCont) {
        ArrayList<String> newLabels = new ArrayList<>(3);
        newLabels.add(nAfter);
        newLabels.add(nBrk);
        newLabels.add(nCont);
        this.labelsStack.add(newLabels);
    }

    private String getTopAfterLabel() {
        return this.labelsStack.get(this.labelsStack.size() - 1).get(0);
    }

    private String getTopBrkLabel() {
        return this.labelsStack.get(this.labelsStack.size() - 1).get(1);
    }

    private String getTopContLabel() {
        return this.labelsStack.get(this.labelsStack.size() - 1).get(2);
    }

    private void popLabels() {
        this.labelsStack.remove(this.labelsStack.size() - 1);
    }

    private String getNewLabel(){
        String newLabel = "Label_" + labelCounter;
        labelCounter += 1;
        return newLabel;
    }

    private String underlineOrSpace(int slot) {
        if (0 <= slot && slot <= 3)
            return "_";
        else
            return " ";
    }

    private void branch(Expression exp, String nTrue, String nFalse){
        if (exp instanceof UnaryExpression) {
            UnaryExpression unExp = (UnaryExpression) exp;
            if (unExp.getOperator() == UnaryOperator.not){
                branch(unExp.getOperand(), nFalse, nTrue);
            }
        }
        else if (exp instanceof BinaryExpression) {
            BinaryExpression binExp = (BinaryExpression) exp;
            if (binExp.getBinaryOperator() == BinaryOperator.and) {
                String nNext = getNewLabel();
                branch(binExp.getFirstOperand(), nNext, nFalse);
                addCommand(nNext + ":");
                branch(binExp.getSecondOperand(), nTrue, nFalse);
            }
            else if (binExp.getBinaryOperator() == BinaryOperator.or) {
                String nNext = getNewLabel();
                branch(binExp.getFirstOperand(), nTrue, nNext);
                addCommand(nNext + ":");
                branch(binExp.getSecondOperand(), nTrue, nFalse);
            }
            else {
                String expCommand = exp.accept(this);
                addCommand(expCommand);
                addCommand("ifeq " + nFalse);
                addCommand("goto " + nTrue);
            }
        }
        else if (exp instanceof BoolValue) {
            BoolValue boolValue = (BoolValue) exp;
            if (boolValue.getConstant())
                addCommand("goto " + nTrue);
            else
                addCommand("goto " + nFalse);
        }
        else {
            String expCommand = exp.accept(this);
            addCommand(expCommand);
            addCommand("ifeq " + nFalse);
            addCommand("goto " + nTrue);
        }
    }

    private String makeTypeSignature(Type t) {
        String signature = "";
        if (t instanceof IntType)
            signature += "Ljava/lang/Integer;";
        else if (t instanceof BoolType)
            signature += "Ljava/lang/Boolean;";
        else if (t instanceof StringType)
            signature += "Ljava/lang/String;";
        else if (t instanceof ListType)
            signature += "LList;";
        else if (t instanceof FptrType)
            signature += "LFptr;";
        else if (t instanceof ClassType)
            signature += "L" + ((ClassType) t).getClassName().getName() + ";";
        else if (t instanceof NullType)
            signature += "V";
        return signature;
    }

    private boolean areListsEqual(ListType firstOperand, ListType secondOperand) {
        if (firstOperand.getElementsTypes().size() != secondOperand.getElementsTypes().size())
            return false;
        ArrayList<ListNameType> firstOperandElementTypes = firstOperand.getElementsTypes();
        ArrayList<ListNameType> secondOperandElementTypes = secondOperand.getElementsTypes();

        for (int i = 0; i < firstOperandElementTypes.size(); i++) {
            if (firstOperandElementTypes.get(i).getType() instanceof ListType) {
                if (!(secondOperandElementTypes.get(i).getType() instanceof ListType))
                    return false;
                else if (!areListsEqual((ListType)firstOperandElementTypes.get(i).getType(),
                        (ListType)secondOperandElementTypes.get(i).getType()))
                    return false;
            }
            else {
                if (!firstOperandElementTypes.get(i).getType().toString()
                        .equals(secondOperandElementTypes.get(i).getType().toString()))
                    return false;
            }
        }

        return true;
    }

    private String makeFuncArgsSignature(ArrayList<Type> argsType) {
        String signature = "";
        for (Type type : argsType) {
            signature += makeTypeSignature(type);
        }
        return signature;
    }

    private void initializeType(Type fieldType) {
        if (fieldType instanceof IntType) {
            addCommand("new java/lang/Integer");
            addCommand("dup");
            addCommand("ldc 0");
            addCommand("invokespecial java/lang/Integer/<init>(I)V");
        }
        else if (fieldType instanceof BoolType) {
            addCommand("new java/lang/Boolean");
            addCommand("dup");
            addCommand("ldc 0");
            addCommand("invokespecial java/lang/Boolean/<init>(Z)V");
        }
        else if (fieldType instanceof StringType) {
            addCommand("ldc \"\"");
        }
        else if (fieldType instanceof ListType) {
            ListType listType = (ListType) fieldType;
            addCommand("new List");
            addCommand("dup");

            addCommand("new java/util/ArrayList");
            addCommand("dup");
            addCommand("invokespecial java/util/ArrayList/<init>()V");
            for (ListNameType listNameType : listType.getElementsTypes()) {
                addCommand("dup");
                initializeType(listNameType.getType());
                addCommand("invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z");
                addCommand("pop");
            }

            addCommand("invokespecial List/<init>(Ljava/util/ArrayList;)V");
        }
        else if (fieldType instanceof FptrType) {
            addCommand("aconst_null");
        }
        else if (fieldType instanceof ClassType) {
            addCommand("aconst_null");
        }
    }

    public ArrayList<Type> getVarDecArrayTypes(ArrayList<VarDeclaration> varDecArray) {
        ArrayList<Type> types = new ArrayList<>();
        for (VarDeclaration varDeclaration : varDecArray) {
            types.add(varDeclaration.getType());
        }
        return types;
    }

    private void addDefaultConstructor() {
        addCommand(".method public <init>()V");
        addCommand(".limit stack 128");
        addCommand(".limit locals 128");

        addCommand("aload_0");
        if (this.currentClass.getParentClassName() != null)
            addCommand("invokespecial " + this.currentClass.getParentClassName().getName() + "/<init>()V");
        else
            addCommand("invokespecial java/lang/Object/<init>()V");

        for (FieldDeclaration fieldDeclaration : this.currentClass.getFields()) {
            addCommand("aload_0");
            initializeType(fieldDeclaration.getVarDeclaration().getType());
            addCommand("putfield " + this.currentClass.getClassName().getName()
                    + "/" + fieldDeclaration.getVarDeclaration().getVarName().getName()
                    + " " + makeTypeSignature(fieldDeclaration.getVarDeclaration().getType()));
        }

        addCommand("return");
        addCommand(".end method");
    }

    private void addStaticMainMethod() {
        addCommand(".method public static main([Ljava/lang/String;)V");
        addCommand(".limit stack 128");
        addCommand(".limit locals 128");
        addCommand("new Main");
        addCommand("invokespecial Main/<init>()V");
        addCommand("return");
        addCommand(".end method");
    }

    private int slotOf(String identifier) {
        if (identifier.equals("")) {
            return this.currentSlots.size()-1 + this.tempVarNumber;
        }
        for (int i = 0; i < this.currentSlots.size(); i++) {
            if (this.currentSlots.get(i).equals(identifier))
                return i;
        }
        return 0;
    }

    @Override
    public String visit(Program program) {
        for (ClassDeclaration sophiaClass : program.getClasses()) {
            createFile(sophiaClass.getClassName().getName());
            sophiaClass.accept(this);
        }
        return null;
    }

    @Override
    public String visit(ClassDeclaration classDeclaration) {
        this.currentClass = classDeclaration;
        this.expressionTypeChecker.setCurrentClass(classDeclaration);

        addCommand(".class public " + classDeclaration.getClassName().getName());
        if (classDeclaration.getParentClassName() == null)
            addCommand(".super java/lang/Object");
        else
            addCommand(".super " + classDeclaration.getParentClassName().getName());
        addBlankLine();

        for (FieldDeclaration fieldDeclaration : classDeclaration.getFields()) {
            fieldDeclaration.accept(this);
        }
        if (classDeclaration.getFields().size() != 0)
            addBlankLine();

        if (classDeclaration.getConstructor() != null)
            classDeclaration.getConstructor().accept(this);
        else
            addDefaultConstructor();
        addBlankLine();

        for (MethodDeclaration methodDeclaration : classDeclaration.getMethods()) {
            methodDeclaration.accept(this);
            addBlankLine();
        }
        return null;
    }

    @Override
    public String visit(ConstructorDeclaration constructorDeclaration) {
        if (constructorDeclaration.getArgs().size() != 0) {
            addDefaultConstructor();
            addBlankLine();
        }
        this.visit((MethodDeclaration) constructorDeclaration);
        addBlankLine();
        if (constructorDeclaration.getMethodName().getName().equals("Main")) {
            addStaticMainMethod();
        }
        return null;
    }

    @Override
    public String visit(MethodDeclaration methodDeclaration) {
        this.currentMethod = methodDeclaration;
        this.expressionTypeChecker.setCurrentMethod(methodDeclaration);
        this.labelCounter = 0;
        this.labelsStack.clear();
        this.currentSlots.clear();
        this.currentSlots.add("this");

        if(methodDeclaration instanceof ConstructorDeclaration) {
            addCommand(".method public <init>(" + makeFuncArgsSignature(getVarDecArrayTypes(methodDeclaration.getArgs())) + ")V");
            addCommand(".limit stack 128");
            addCommand(".limit locals 128");

            addCommand("aload_0");
            if (this.currentClass.getParentClassName() != null)
                addCommand("invokespecial " + this.currentClass.getParentClassName().getName() + "/<init>()V");
            else
                addCommand("invokespecial java/lang/Object/<init>()V");

            for (FieldDeclaration fieldDeclaration : this.currentClass.getFields()) {
                addCommand("aload_0");
                initializeType(fieldDeclaration.getVarDeclaration().getType());
                addCommand("putfield " + this.currentClass.getClassName().getName()
                        + "/" + fieldDeclaration.getVarDeclaration().getVarName().getName()
                        + " " + makeTypeSignature(fieldDeclaration.getVarDeclaration().getType()));
            }
        }
        else {
            addCommand(".method public " + methodDeclaration.getMethodName().getName()
                    + "(" + makeFuncArgsSignature(getVarDecArrayTypes(methodDeclaration.getArgs())) + ")"
                    + makeTypeSignature(methodDeclaration.getReturnType()));
            addCommand(".limit stack 128");
            addCommand(".limit locals 128");
        }

        for (VarDeclaration varDeclaration: methodDeclaration.getArgs()) {
            varDeclaration.accept(this);
        }

        for (VarDeclaration varDeclaration : methodDeclaration.getLocalVars()) {
            varDeclaration.accept(this);
            int slot = slotOf(varDeclaration.getVarName().getName());
            initializeType(varDeclaration.getType());
            addCommand("astore" + underlineOrSpace(slot) + slot);
        }

        for (Statement statement : methodDeclaration.getBody()) {
            String nAfter = getNewLabel();
            pushLabels(nAfter, nAfter, nAfter);
            statement.accept(this);
            popLabels();
            addCommand(nAfter + ":");
        }
        if (!methodDeclaration.getDoesReturn()) {
            addCommand("return");
        }
        addCommand(".end method");
        return null;
    }

    @Override
    public String visit(FieldDeclaration fieldDeclaration) {
        addCommand(".field public " + fieldDeclaration.getVarDeclaration().getVarName().getName() + " "
                + makeTypeSignature(fieldDeclaration.getVarDeclaration().getType()));
        return null;
    }

    @Override
    public String visit(VarDeclaration varDeclaration) {
        this.currentSlots.add(varDeclaration.getVarName().getName());
        return null;
    }

    @Override
    public String visit(AssignmentStmt assignmentStmt) {
        BinaryExpression assignmentExpression = new BinaryExpression(assignmentStmt.getlValue(),
                assignmentStmt.getrValue(), BinaryOperator.assign);
        addCommand(assignmentExpression.accept(this));
        addCommand("pop");
        addCommand("goto " + getTopAfterLabel());
        return null;
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        for (Statement statement : blockStmt.getStatements()) {
            String nAfter = getNewLabel();
            pushLabels(nAfter, getTopBrkLabel(), getTopContLabel());
            statement.accept(this);
            popLabels();
            addCommand(nAfter + ":");
        }
        addCommand("goto " + getTopAfterLabel());
        return null;
    }

    @Override
    public String visit(ConditionalStmt conditionalStmt) {
        String nTrue = getNewLabel();
        String nFalse = getNewLabel();
        branch(conditionalStmt.getCondition(), nTrue, nFalse);

        addCommand(nTrue + ":");
        pushLabels(getTopAfterLabel(), getTopBrkLabel(), getTopContLabel());
        conditionalStmt.getThenBody().accept(this);
        popLabels();

        addCommand(nFalse + ":");
        if (conditionalStmt.getElseBody() != null) {
            pushLabels(getTopAfterLabel(), getTopBrkLabel(), getTopContLabel());
            conditionalStmt.getElseBody().accept(this);
            popLabels();
        }

        addCommand("goto " + getTopAfterLabel());
        return null;
    }

    @Override
    public String visit(MethodCallStmt methodCallStmt) {
        expressionTypeChecker.setIsInMethodCallStmt(true);
        addCommand(methodCallStmt.getMethodCall().accept(this));
        expressionTypeChecker.setIsInMethodCallStmt(false);
        FptrType fptrType = (FptrType) methodCallStmt.getMethodCall().getInstance().accept(this.expressionTypeChecker);
        if (!(fptrType.getReturnType() instanceof NullType))
            addCommand("pop");
        addCommand("goto " + getTopAfterLabel());
        return null;
    }

    @Override
    public String visit(PrintStmt print) {
        Type argType = print.getArg().accept(expressionTypeChecker);
        addCommand("getstatic java/lang/System/out Ljava/io/PrintStream;");
        addCommand(print.getArg().accept(this));

        String signature = "";
        if (argType instanceof IntType) {
            signature = "I";
        }
        else if (argType instanceof BoolType) {
            signature = "Z";
        }
        else {
            signature = makeTypeSignature(argType);
        }

        addCommand("invokevirtual java/io/PrintStream/print(" + signature + ")V");
        addCommand("goto " + getTopAfterLabel());
        return null;
    }

    @Override
    public String visit(ReturnStmt returnStmt) {
        Type returnType = returnStmt.getReturnedExpr().accept(expressionTypeChecker);
        if(returnType instanceof NullType) {
            addCommand("return");
        }
        else if (returnType instanceof IntType) {
            addCommand("new java/lang/Integer");
            addCommand("dup");
            addCommand(returnStmt.getReturnedExpr().accept(this));
            addCommand("invokespecial java/lang/Integer/<init>(I)V");
            addCommand("areturn");
        }
        else if (returnType instanceof BoolType) {
            addCommand("new java/lang/Boolean");
            addCommand("dup");
            addCommand(returnStmt.getReturnedExpr().accept(this));
            addCommand("invokespecial java/lang/Boolean/<init>(Z)V");
            addCommand("areturn");
        }
        else {
            addCommand(returnStmt.getReturnedExpr().accept(this));
            addCommand("areturn");
        }
        return null;
    }

    @Override
    public String visit(BreakStmt breakStmt) {
        addCommand("goto " + getTopBrkLabel());
        return null;
    }

    @Override
    public String visit(ContinueStmt continueStmt) {
        addCommand("goto " + getTopContLabel());
        return null;
    }

    @Override
    public String visit(ForeachStmt foreachStmt) {
        String nAfter = getTopAfterLabel();

        String nInit = getNewLabel();
        String nCond = getNewLabel();
        String nBody = getNewLabel();
        String nUpdate = getNewLabel();

        int listSize = ((ListType)foreachStmt.getList().accept(this.expressionTypeChecker)).getElementsTypes().size();

        int foreachVarSlot = slotOf(foreachStmt.getVariable().getName());
        String varSignature = "";
        varSignature += makeTypeSignature(((ListType)foreachStmt.getList().accept(this.expressionTypeChecker))
                .getElementsTypes().get(0).getType());
        varSignature = varSignature.substring(1, varSignature.length() - 1);

        this.tempVarNumber++;
        int indexTempSlot = slotOf("");


        /*init*/
        addCommand(nInit + ":");
        addCommand("ldc 0") ;
        addCommand("istore" + underlineOrSpace(indexTempSlot) + indexTempSlot);

        /*condition check*/
        addCommand(nCond + ":");
        addCommand("iload" + underlineOrSpace(indexTempSlot) + indexTempSlot);
        addCommand("ldc " + listSize);
        addCommand("if_icmpge " + nAfter);

        /*body*/
        addCommand(nBody + ":");
        addCommand(foreachStmt.getList().accept(this));
        addCommand("iload" + underlineOrSpace(indexTempSlot) + indexTempSlot);
        addCommand("invokevirtual List/getElement(I)Ljava/lang/Object;");
        addCommand("checkcast " + varSignature);
        addCommand("astore" + underlineOrSpace(foreachVarSlot) + foreachVarSlot);
        pushLabels(nUpdate, nAfter, nUpdate);
        foreachStmt.getBody().accept(this);
        popLabels();

        /*update*/
        addCommand(nUpdate + ":");
        addCommand("iload" + underlineOrSpace(indexTempSlot) + indexTempSlot);
        addCommand("iconst_1");
        addCommand("iadd");
        addCommand("istore" + underlineOrSpace(indexTempSlot) + indexTempSlot);
        addCommand("goto " + nCond);

        this.tempVarNumber--;
        this.currentSlots.remove(this.currentSlots.size() - 1);

        addCommand("goto " + getTopAfterLabel());

        return null;
    }

    @Override
    public String visit(ForStmt forStmt) {
        String nAfter = getTopAfterLabel();

        String nInit = getNewLabel();
        String nCond = getNewLabel();
        String nBody = getNewLabel();
        String nUpdate = getNewLabel();

        addCommand(nInit + ":");
        if (forStmt.getInitialize() != null) {
            pushLabels(nCond, nAfter, nCond);
            forStmt.getInitialize().accept(this);
            popLabels();
        }

        addCommand(nCond + ":");
        if (forStmt.getCondition() != null) {
            branch(forStmt.getCondition(), nBody, nAfter);
        }

        addCommand(nBody + ":");
        if (forStmt.getBody() != null) {
            pushLabels(nUpdate, nAfter, nUpdate);
            forStmt.getBody().accept(this);
            popLabels();
        }

        addCommand(nUpdate + ":");
        if (forStmt.getUpdate() != null) {
            pushLabels(nCond, nAfter, nCond);
            forStmt.getUpdate().accept(this);
            popLabels();
        }

        addCommand("goto " + getTopAfterLabel());

        return null;
    }

    @Override
    public String visit(BinaryExpression binaryExpression) {
        BinaryOperator operator = binaryExpression.getBinaryOperator();
        String commands = "";
        if (operator == BinaryOperator.add) {
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += binaryExpression.getSecondOperand().accept(this);
            commands += "iadd\n";
        }
        else if (operator == BinaryOperator.sub) {
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += binaryExpression.getSecondOperand().accept(this);
            commands += "isub\n";
        }
        else if (operator == BinaryOperator.mult) {
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += binaryExpression.getSecondOperand().accept(this);
            commands += "imul\n";
        }
        else if (operator == BinaryOperator.div) {
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += binaryExpression.getSecondOperand().accept(this);
            commands += "idiv\n";
        }
        else if (operator == BinaryOperator.mod) {
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += binaryExpression.getSecondOperand().accept(this);
            commands += "irem\n";
        }
        else if((operator == BinaryOperator.gt) || (operator == BinaryOperator.lt)) {
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += binaryExpression.getSecondOperand().accept(this);

            String nTrue = getNewLabel();
            String nFalse = getNewLabel();
            String nAfter = getNewLabel();
            if (operator == BinaryOperator.gt)
                commands += "if_icmpgt " + nTrue +"\n";
            else
                commands += "if_icmplt " + nTrue +"\n";
            commands += nFalse + ":\n";
            commands += "ldc 0\n";
            commands += "goto " + nAfter + "\n";
            commands += nTrue + ":\n";
            commands += "ldc 1\n";
            commands += nAfter + ":\n";
        }
        else if((operator == BinaryOperator.eq) || (operator == BinaryOperator.neq)) {
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += binaryExpression.getSecondOperand().accept(this);

            String nTrue = getNewLabel();
            String nFalse = getNewLabel();
            String nAfter = getNewLabel();

            Type operandsType = binaryExpression.getFirstOperand().accept(this.expressionTypeChecker);

            if ((operandsType instanceof IntType) || (operandsType instanceof BoolType)) {
                if (operator == BinaryOperator.eq)
                    commands += "if_icmpeq " + nTrue +"\n";
                else
                    commands += "if_icmpne " + nTrue +"\n";
                commands += nFalse + ":\n";
                commands += "ldc 0\n";
                commands += "goto " + nAfter + "\n";
                commands += nTrue + ":\n";
                commands += "ldc 1\n";
                commands += nAfter + ":\n";
            }
            else if (operandsType instanceof StringType) {
                commands += "invokevirtual java/lang/String/equals(Ljava/lang/Object;)Z\n";
                if (operator == BinaryOperator.neq) {
                    commands += "ldc 1\n";
                    commands += "ixor\n";
                }
            }
            else if (operandsType instanceof ListType) {
                ListType firstOperand = (ListType) binaryExpression.getFirstOperand().accept(this.expressionTypeChecker);
                ListType secondOperand = (ListType) binaryExpression.getSecondOperand().accept(this.expressionTypeChecker);
                boolean listsAreEqual = areListsEqual(firstOperand, secondOperand);
                if (listsAreEqual)
                    commands += "ldc 1\n";
                else
                    commands += "ldc 0\n";
            }
            else {
                if (operator == BinaryOperator.eq)
                    commands += "if_acmpeq " + nTrue +"\n";
                else
                    commands += "if_acmpne " + nTrue +"\n";
                commands += nFalse + ":\n";
                commands += "ldc 0\n";
                commands += "goto " + nAfter + "\n";
                commands += nTrue + ":\n";
                commands += "ldc 1\n";
                commands += nAfter + ":\n";
            }
        }
        else if(operator == BinaryOperator.and) {
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += binaryExpression.getSecondOperand().accept(this);
            commands += "iand\n";
        }
        else if(operator == BinaryOperator.or) {
            commands += binaryExpression.getFirstOperand().accept(this);
            commands += binaryExpression.getSecondOperand().accept(this);
            commands += "ior\n";
        }
        else if(operator == BinaryOperator.assign) {
            Type firstType = binaryExpression.getFirstOperand().accept(expressionTypeChecker);
            String secondOperandCommands = binaryExpression.getSecondOperand().accept(this);
            if(firstType instanceof ListType) {
                // make new list with List copy constructor with the second operand commands
                // (add these commands to secondOperandCommands)
                secondOperandCommands = "new List\n" + "dup\n" + secondOperandCommands + "invokespecial List/<init>(LList;)V\n";
            }
            if(binaryExpression.getFirstOperand() instanceof Identifier) {
                Type secondType = binaryExpression.getSecondOperand().accept(this.expressionTypeChecker);
                int slot = slotOf(((Identifier)binaryExpression.getFirstOperand()).getName());

                if (secondType instanceof IntType) {
                    commands += "new java/lang/Integer\n";
                    commands += "dup\n";
                    commands += secondOperandCommands;
                    commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                    commands += "dup\n";
                    commands += "astore" + underlineOrSpace(slot) + slot + "\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                }
                else if (secondType instanceof BoolType) {
                    commands += "new java/lang/Boolean\n";
                    commands += "dup\n";
                    commands += secondOperandCommands;
                    commands += "invokespecial java/lang/Boolean/<init>(Z)V\n";
                    commands += "dup\n";
                    commands += "astore" + underlineOrSpace(slot) + slot + "\n";
                    commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
                }
                else {
                    commands += secondOperandCommands;
                    commands += "dup\n";
                    commands += "astore" + underlineOrSpace(slot) + slot + "\n";
                }
            }
            else if(binaryExpression.getFirstOperand() instanceof ListAccessByIndex) {
                Type secondType = binaryExpression.getSecondOperand().accept(this.expressionTypeChecker);
                ListAccessByIndex firstOperandListAccess = (ListAccessByIndex) binaryExpression.getFirstOperand();
                this.tempVarNumber++;
                int tempSlot = slotOf("");
                if (secondType instanceof IntType) {
                    commands += "new java/lang/Integer\n";
                    commands += "dup\n";
                    commands += secondOperandCommands;
                    commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                    commands += "astore" + underlineOrSpace(tempSlot) + tempSlot + "\n";

                    commands += firstOperandListAccess.getInstance().accept(this);
                    commands += firstOperandListAccess.getIndex().accept(this);
                    commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                    commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                }
                else if (secondType instanceof BoolType) {
                    commands += "new java/lang/Boolean\n";
                    commands += "dup\n";
                    commands += secondOperandCommands;
                    commands += "invokespecial java/lang/Boolean/<init>(Z)V\n";
                    commands += "astore" + underlineOrSpace(tempSlot) + tempSlot + "\n";

                    commands += firstOperandListAccess.getInstance().accept(this);
                    commands += firstOperandListAccess.getIndex().accept(this);
                    commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                    commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                    commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
                }
                else {
                    commands += secondOperandCommands;
                    commands += "astore" + underlineOrSpace(tempSlot) + tempSlot + "\n";

                    commands += firstOperandListAccess.getInstance().accept(this);
                    commands += firstOperandListAccess.getIndex().accept(this);
                    commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                    commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                }
                this.tempVarNumber--;
            }
            else if(binaryExpression.getFirstOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) binaryExpression.getFirstOperand()).getInstance();
                Type memberType = binaryExpression.getFirstOperand().accept(expressionTypeChecker);
                String memberName = ((ObjectOrListMemberAccess) binaryExpression.getFirstOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    ListType instanceListType = (ListType) instanceType;
                    int index;
                    for (index = 0; index < instanceListType.getElementsTypes().size(); index++) {
                        if (instanceListType.getElementsTypes().get(index).getName().getName().equals(memberName))
                            break;
                    }
                    Type secondType = binaryExpression.getSecondOperand().accept(this.expressionTypeChecker);
                    this.tempVarNumber++;
                    int tempSlot = slotOf("");
                    if (secondType instanceof IntType) {
                        commands += "new java/lang/Integer\n";
                        commands += "dup\n";
                        commands += secondOperandCommands;
                        commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                        commands += "astore" + underlineOrSpace(tempSlot) + tempSlot + "\n";

                        commands += instance.accept(this);
                        commands += "ldc " + index + "\n";
                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                        commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                        commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    }
                    else if (secondType instanceof BoolType) {
                        commands += "new java/lang/Boolean\n";
                        commands += "dup\n";
                        commands += secondOperandCommands;
                        commands += "invokespecial java/lang/Boolean/<init>(Z)V\n";
                        commands += "astore" + underlineOrSpace(tempSlot) + tempSlot + "\n";

                        commands += instance.accept(this);
                        commands += "ldc " + index + "\n";
                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                        commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                        commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
                    }
                    else {
                        commands += secondOperandCommands;
                        commands += "astore" + underlineOrSpace(tempSlot) + tempSlot + "\n";

                        commands += instance.accept(this);
                        commands += "ldc " + index + "\n";
                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                        commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                    }
                    this.tempVarNumber--;
                }
                else if(instanceType instanceof ClassType) {
                    ClassType instanceClassType = (ClassType) instanceType;
                    Type secondType = binaryExpression.getSecondOperand().accept(this.expressionTypeChecker);
                    this.tempVarNumber++;
                    int tempSlot = slotOf("");
                    if (secondType instanceof IntType) {
                        commands += "new java/lang/Integer\n";
                        commands += "dup\n";
                        commands += secondOperandCommands;
                        commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                        commands += "astore" + underlineOrSpace(tempSlot) + tempSlot + "\n";

                        commands += instance.accept(this);
                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                        commands += "putfield " + instanceClassType.getClassName().getName()
                                + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";

                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                        commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    }
                    else if (secondType instanceof BoolType) {
                        commands += "new java/lang/Boolean\n";
                        commands += "dup\n";
                        commands += secondOperandCommands;
                        commands += "invokespecial java/lang/Boolean/<init>(Z)V\n";
                        commands += "astore" + underlineOrSpace(tempSlot) + tempSlot + "\n";

                        commands += instance.accept(this);
                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                        commands += "putfield " + instanceClassType.getClassName().getName()
                                + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";

                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                        commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
                    }
                    else {
                        commands += secondOperandCommands;
                        commands += "astore" + underlineOrSpace(tempSlot) + tempSlot + "\n";

                        commands += instance.accept(this);
                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                        commands += "putfield " + instanceClassType.getClassName().getName()
                                + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";

                        commands += "aload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                    }
                    this.tempVarNumber--;
                }
            }
        }
        return commands;
    }

    @Override
    public String visit(UnaryExpression unaryExpression) {
        UnaryOperator operator = unaryExpression.getOperator();
        String commands = "";
        if(operator == UnaryOperator.minus) {
            commands += unaryExpression.getOperand().accept(this);
            commands += "ineg\n";
        }
        else if(operator == UnaryOperator.not) {
            commands += unaryExpression.getOperand().accept(this);
            commands += "ldc 1\n";
            commands += "ixor\n";
        }
        else if((operator == UnaryOperator.predec) || (operator == UnaryOperator.preinc)) {
            if(unaryExpression.getOperand() instanceof Identifier) {
                int slot = slotOf(((Identifier) unaryExpression.getOperand()).getName());

                commands += "new java/lang/Integer\n";
                commands += "dup\n";

                commands += unaryExpression.getOperand().accept(this);
                if (operator == UnaryOperator.preinc)
                    commands += "ldc 1\n";
                else
                    commands += "ldc -1\n";
                commands += "iadd\n";
                commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                commands += "dup\n";
                commands += "astore" + underlineOrSpace(slot) + slot + "\n";
                commands += "invokevirtual java/lang/Integer/intValue()I\n";
            }

            else if(unaryExpression.getOperand() instanceof ListAccessByIndex) {
                ListAccessByIndex unaryListAccess = (ListAccessByIndex) unaryExpression.getOperand();

                this.tempVarNumber++;
                int tempSlotInstance = slotOf("");
                this.tempVarNumber++;
                int tempSlotIndex = slotOf("");
                this.tempVarNumber++;
                int tempSlotResult = slotOf("");

                commands += unaryListAccess.getInstance().accept(this);
                commands += "astore" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                commands += unaryListAccess.getIndex().accept(this);
                commands += "invokevirtual java/lang/Integer/intValue()I\n";
                commands += "istore" + underlineOrSpace(tempSlotIndex) + tempSlotIndex + "\n";

                commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                commands += "iload" + underlineOrSpace(tempSlotIndex) + tempSlotIndex + "\n";
                commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                commands += "checkcast java/lang/Integer\n";
                commands += "invokevirtual java/lang/Integer/intValue()I\n";
                if (operator == UnaryOperator.preinc)
                    commands += "ldc 1\n";
                else
                    commands += "ldc -1\n";
                commands += "iadd\n";
                commands += "istore" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                commands += "iload" + underlineOrSpace(tempSlotIndex) + tempSlotIndex + "\n";
                commands += "new java/lang/Integer\n";
                commands += "dup\n";
                commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";
                commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                this.tempVarNumber -= 3;

            }
            else if(unaryExpression.getOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance();
                Type memberType = unaryExpression.getOperand().accept(expressionTypeChecker);
                String memberName = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    ListType instanceListType = (ListType) instanceType;
                    int memberIndex;
                    for (memberIndex = 0; memberIndex < instanceListType.getElementsTypes().size(); memberIndex++) {
                        if (instanceListType.getElementsTypes().get(memberIndex).getName().getName().equals(memberName))
                            break;
                    }

                    ListAccessByIndex unaryListAccess = (ListAccessByIndex) unaryExpression.getOperand();

                    this.tempVarNumber++;
                    int tempSlotInstance = slotOf("");
                    this.tempVarNumber++;
                    int tempSlotResult = slotOf("");

                    commands += unaryListAccess.getInstance().accept(this);
                    commands += "astore" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";

                    commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                    commands += "ldc " + memberIndex + "\n";
                    commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                    commands += "checkcast java/lang/Integer\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    if (operator == UnaryOperator.preinc)
                        commands += "ldc 1\n";
                    else
                        commands += "ldc -1\n";
                    commands += "iadd\n";
                    commands += "istore" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                    commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                    commands += "ldc " + memberIndex + "\n";
                    commands += "new java/lang/Integer\n";
                    commands += "dup\n";
                    commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";
                    commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                    commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                    this.tempVarNumber -= 2;
                }
                else if(instanceType instanceof ClassType) {
                    ClassType classType = (ClassType) instanceType;

                    this.tempVarNumber++;
                    int tempSlotInstance = slotOf("");
                    this.tempVarNumber++;
                    int tempSlotResult = slotOf("");

                    commands += instance.accept(this);
                    commands += "astore" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";

                    commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                    commands += "getfield " + classType.getClassName().getName() + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    if (operator == UnaryOperator.preinc)
                        commands += "ldc 1\n";
                    else
                        commands += "ldc -1\n";
                    commands += "iadd\n";
                    commands += "istore" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                    commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                    commands += "new java/lang/Integer\n";
                    commands += "dup\n";
                    commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";
                    commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                    commands += "putfield " + classType.getClassName().getName() + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";

                    commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                    this.tempVarNumber -= 2;
                }
            }
        }
        else if((operator == UnaryOperator.postdec) || (operator == UnaryOperator.postinc)) {
            if(unaryExpression.getOperand() instanceof Identifier) {
                int slot = slotOf(((Identifier) unaryExpression.getOperand()).getName());

                this.tempVarNumber++;
                int tempSlot = slotOf("");

                commands += unaryExpression.getOperand().accept(this);
                commands += "istore" + underlineOrSpace(tempSlot) + tempSlot + "\n";

                commands += "new java/lang/Integer\n";
                commands += "dup\n";
                commands += "iload" + underlineOrSpace(tempSlot) + tempSlot + "\n";
                if (operator == UnaryOperator.postinc)
                    commands += "ldc 1\n";
                else
                    commands += "ldc -1\n";
                commands += "iadd\n";
                commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                commands += "astore" + underlineOrSpace(slot) + slot + "\n";

                commands += "iload" + underlineOrSpace(tempSlot) + tempSlot + "\n";

                this.tempVarNumber--;
            }
            else if(unaryExpression.getOperand() instanceof ListAccessByIndex) {
                ListAccessByIndex unaryListAccess = (ListAccessByIndex) unaryExpression.getOperand();

                this.tempVarNumber++;
                int tempSlotInstance = slotOf("");
                this.tempVarNumber++;
                int tempSlotIndex = slotOf("");
                this.tempVarNumber++;
                int tempSlotResult = slotOf("");

                commands += unaryListAccess.getInstance().accept(this);
                commands += "astore" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                commands += unaryListAccess.getIndex().accept(this);
                commands += "invokevirtual java/lang/Integer/intValue()I\n";
                commands += "istore" + underlineOrSpace(tempSlotIndex) + tempSlotIndex + "\n";

                commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                commands += "iload" + underlineOrSpace(tempSlotIndex) + tempSlotIndex + "\n";
                commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                commands += "checkcast java/lang/Integer\n";
                commands += "invokevirtual java/lang/Integer/intValue()I\n";
                commands += "istore" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                commands += "iload" + underlineOrSpace(tempSlotIndex) + tempSlotIndex + "\n";
                commands += "new java/lang/Integer\n";
                commands += "dup\n";
                commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";
                if (operator == UnaryOperator.postinc)
                    commands += "ldc 1\n";
                else
                    commands += "ldc -1\n";
                commands += "iadd\n";
                commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                this.tempVarNumber -= 3;
            }
            else if(unaryExpression.getOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance();
                Type memberType = unaryExpression.getOperand().accept(expressionTypeChecker);
                String memberName = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    ListType instanceListType = (ListType) instanceType;
                    int memberIndex;
                    for (memberIndex = 0; memberIndex < instanceListType.getElementsTypes().size(); memberIndex++) {
                        if (instanceListType.getElementsTypes().get(memberIndex).getName().getName().equals(memberName))
                            break;
                    }

                    ListAccessByIndex unaryListAccess = (ListAccessByIndex) unaryExpression.getOperand();

                    this.tempVarNumber++;
                    int tempSlotInstance = slotOf("");
                    this.tempVarNumber++;
                    int tempSlotResult = slotOf("");

                    commands += unaryListAccess.getInstance().accept(this);
                    commands += "astore" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";

                    commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                    commands += "ldc " + memberIndex + "\n";
                    commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";
                    commands += "checkcast java/lang/Integer\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    commands += "istore" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                    commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                    commands += "ldc " + memberIndex + "\n";
                    commands += "new java/lang/Integer\n";
                    commands += "dup\n";
                    commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";
                    if (operator == UnaryOperator.postinc)
                        commands += "ldc 1\n";
                    else
                        commands += "ldc -1\n";
                    commands += "iadd\n";
                    commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                    commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                    this.tempVarNumber -= 2;
                }
                else if(instanceType instanceof ClassType) {
                    ClassType classType = (ClassType) instanceType;

                    this.tempVarNumber++;
                    int tempSlotInstance = slotOf("");
                    this.tempVarNumber++;
                    int tempSlotResult = slotOf("");

                    commands += instance.accept(this);
                    commands += "astore" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";

                    commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                    commands += "getfield " + classType.getClassName().getName() + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    commands += "istore" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                    commands += "aload" + underlineOrSpace(tempSlotInstance) + tempSlotInstance + "\n";
                    commands += "new java/lang/Integer\n";
                    commands += "dup\n";
                    commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";
                    if (operator == UnaryOperator.postinc)
                        commands += "ldc 1\n";
                    else
                        commands += "ldc -1\n";
                    commands += "iadd\n";
                    commands += "invokespecial java/lang/Integer/<init>(I)V\n";
                    commands += "putfield " + classType.getClassName().getName() + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";

                    commands += "iload" + underlineOrSpace(tempSlotResult) + tempSlotResult + "\n";

                    this.tempVarNumber -= 2;
                }
            }
        }
        return commands;
    }

    @Override
    public String visit(ObjectOrListMemberAccess objectOrListMemberAccess) {
        Type memberType = objectOrListMemberAccess.accept(expressionTypeChecker);
        Type instanceType = objectOrListMemberAccess.getInstance().accept(expressionTypeChecker);
        String memberName = objectOrListMemberAccess.getMemberName().getName();
        String commands = "";
        if(instanceType instanceof ClassType) {
            String className = ((ClassType) instanceType).getClassName().getName();
            try {
                SymbolTable classSymbolTable = ((ClassSymbolTableItem) SymbolTable.root.getItem(ClassSymbolTableItem.START_KEY + className, true)).getClassSymbolTable();
                try {
                    classSymbolTable.getItem(FieldSymbolTableItem.START_KEY + memberName, true);
                    commands += objectOrListMemberAccess.getInstance().accept(this);
                    commands += "getfield " + className + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    if (memberType instanceof IntType) {
                        commands += "invokevirtual java/lang/Integer/intValue()I\n";
                    }
                    else if (memberType instanceof BoolType) {
                        commands += "invokevirtual java/lang/Boolean/booleanValue()I\n";
                    }
                } catch (ItemNotFoundException memberIsMethod) {
                    commands += "new Fptr\n";
                    commands += "dup\n";
                    commands += objectOrListMemberAccess.getInstance().accept(this);
                    commands += "ldc \"" + memberName + "\"\n";
                    commands += "invokespecial Fptr/<init>(Ljava/lang/Object;Ljava/lang/String;)V\n";
                }
            } catch (ItemNotFoundException classNotFound) {
            }
        }
        else if(instanceType instanceof ListType) {
            ListType listType = (ListType) instanceType;
            int index;
            for (index = 0; index < listType.getElementsTypes().size(); index++) {
                if (listType.getElementsTypes().get(index).getName().getName().equals(memberName))
                    break;
            }
            commands += objectOrListMemberAccess.getInstance().accept(this);
            commands += "ldc " + index + "\n";
            commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";

            Type elementType = listType.getElementsTypes().get(index).getType();
            if (elementType instanceof BoolType) {
                commands += "checkcast java/lang/Boolean\n";
                commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
            }
            else if (elementType instanceof ClassType) {
                commands += "checkcast " + ((ClassType)elementType).getClassName().getName() + "\n";
            }
            else if (elementType instanceof IntType) {
                commands += "checkcast java/lang/Integer\n";
                commands += "invokevirtual java/lang/Integer/intValue()I\n";
            }
            else if (elementType instanceof StringType) {
                commands += "checkcast java/lang/String\n";
            }
            else if (elementType instanceof ListType) {
                commands += "checkcast List\n";
            }
            else if (elementType instanceof FptrType) {
                commands += "checkcast Fptr\n";
            }
        }
        return commands;
    }

    @Override
    public String visit(Identifier identifier) {
        String commands = "";
        int slot = slotOf(identifier.getName());

        try {
            ClassSymbolTableItem classSymbolTableItem = (ClassSymbolTableItem) SymbolTable.root.getItem(ClassSymbolTableItem.START_KEY + this.currentClass.getClassName().getName(), true);
            SymbolTable classSymbolTable = classSymbolTableItem.getClassSymbolTable();
            MethodSymbolTableItem methodSymbolTableItem = (MethodSymbolTableItem) classSymbolTable.getItem(MethodSymbolTableItem.START_KEY + this.currentMethod.getMethodName().getName(), true);
            SymbolTable methodSymbolTable = methodSymbolTableItem.getMethodSymbolTable();
            LocalVariableSymbolTableItem localVariableSymbolTableItem = (LocalVariableSymbolTableItem) methodSymbolTable.getItem(LocalVariableSymbolTableItem.START_KEY + identifier.getName(), true);
            Type varType = localVariableSymbolTableItem.getType();
            if (varType instanceof IntType) {
                commands += "aload" + underlineOrSpace(slot) + slot + "\n";
                commands += "invokevirtual java/lang/Integer/intValue()I\n";

            }
            else if (varType instanceof BoolType) {
                commands += "aload" + underlineOrSpace(slot) + slot + "\n";
                commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
            }
            else {
                commands += "aload" + underlineOrSpace(slot) + slot + "\n";
            }
        } catch (ItemNotFoundException ignored) {}

        return commands;
    }

    @Override
    public String visit(ListAccessByIndex listAccessByIndex) {
        String commands = "";
        commands += listAccessByIndex.getInstance().accept(this);
        commands += listAccessByIndex.getIndex().accept(this);
        commands += "invokevirtual List/getElement(I)Ljava/lang/Object;\n";

        ListType instanceType = (ListType) listAccessByIndex.getInstance().accept(expressionTypeChecker);
        Type elementType;
        if (listAccessByIndex.getIndex() instanceof IntValue) {
            elementType = instanceType.getElementsTypes().get(((IntValue)listAccessByIndex.getIndex()).getConstant()).getType();
        }
        else {
            elementType = instanceType.getElementsTypes().get(0).getType();
        }

        if (elementType instanceof BoolType) {
            commands += "checkcast java/lang/Boolean\n";
            commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
        }
        else if (elementType instanceof ClassType) {
            commands += "checkcast " + ((ClassType)elementType).getClassName().getName() + "\n";
        }
        else if (elementType instanceof IntType) {
            commands += "checkcast java/lang/Integer\n";
            commands += "invokevirtual java/lang/Integer/intValue()I\n";
        }
        else if (elementType instanceof ListType) {
            commands += "checkcast List\n";
        }
        else if (elementType instanceof FptrType) {
            commands += "checkcast Fptr\n";
        }
        else if (elementType instanceof StringType) {
            commands += "checkcast java/lang/String\n";
        }

        return commands;
    }

    @Override
    public String visit(MethodCall methodCall) {
        String commands = "";
        commands += methodCall.getInstance().accept(this);
        commands += "new java/util/ArrayList\n";
        commands += "dup\n";
        commands += "invokespecial java/util/ArrayList/<init>()V\n";
        for (Expression methodArgs : methodCall.getArgs()) {
            commands += "dup\n";

            Type argType = methodArgs.accept(expressionTypeChecker);
            if (argType instanceof IntType) {
                commands += "new java/lang/Integer\n";
                commands += "dup\n";
                commands += methodArgs.accept(this);
                commands += "invokespecial java/lang/Integer/<init>(I)V\n";
            }
            else if (argType instanceof BoolType) {
                commands += "new java/lang/Boolean\n";
                commands += "dup\n";
                commands += methodArgs.accept(this);
                commands += "invokespecial java/lang/Boolean/<init>(Z)V\n";
            }
            else {
                commands += methodArgs.accept(this);
            }

            commands += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n";
            commands += "pop\n";
        }

        commands += "invokevirtual Fptr/invoke(Ljava/util/ArrayList;)Ljava/lang/Object;\n";

        FptrType instanceType = (FptrType) methodCall.getInstance().accept(expressionTypeChecker);
        if (instanceType.getReturnType() instanceof BoolType) {
            commands += "checkcast java/lang/Boolean\n";
            commands += "invokevirtual java/lang/Boolean/booleanValue()Z\n";
        }
        else if (instanceType.getReturnType() instanceof ClassType) {
            commands += "checkcast " + ((ClassType)instanceType.getReturnType()).getClassName().getName() + "\n";
        }
        else if (instanceType.getReturnType() instanceof IntType) {
            commands += "checkcast java/lang/Integer\n";
            commands += "invokevirtual java/lang/Integer/intValue()I\n";
        }
        else if (instanceType.getReturnType() instanceof StringType) {
            commands += "checkcast java/lang/String\n";
        }
        else if (instanceType.getReturnType() instanceof NullType) {
            commands += "pop\n"; //is it correct for null?
        }

        return commands;
    }

    @Override
    public String visit(NewClassInstance newClassInstance) {
        String commands = "";
        commands += "new " + newClassInstance.getClassType().getClassName().getName() + "\n";
        commands += "dup\n";

        for (Expression arg : newClassInstance.getArgs()) {
            Type argType = arg.accept(expressionTypeChecker);
            if (argType instanceof IntType) {
                commands += "new java/lang/Integer\n";
                commands += "dup\n";
                commands += arg.accept(this);
                commands += "invokespecial java/lang/Integer/<init>(I)V\n";
            }
            else if (argType instanceof BoolType) {
                commands += "new java/lang/Boolean\n";
                commands += "dup\n";
                commands += arg.accept(this);
                commands += "invokespecial java/lang/Boolean/<init>(Z)V\n";
            }
            else {
                commands += arg.accept(this);
            }
        }
        try {
            ClassDeclaration classDeclaration = ((ClassSymbolTableItem) SymbolTable.root.getItem(ClassSymbolTableItem.START_KEY
                    + newClassInstance.getClassType().getClassName().getName(), true)).getClassDeclaration();
            ArrayList<Type> classConstructorArgTypes = new ArrayList<>();
            if (classDeclaration.getConstructor() != null) {
                for (VarDeclaration argDec : classDeclaration.getConstructor().getArgs())
                    classConstructorArgTypes.add(argDec.getType());
            }
            commands += "invokespecial " + newClassInstance.getClassType().getClassName().getName()
                    + "/<init>(" + makeFuncArgsSignature(classConstructorArgTypes) + ")V\n";
        } catch (ItemNotFoundException ignored) {}
        return commands;
    }

    @Override
    public String visit(ThisClass thisClass) {
        String commands = "";
        commands += "aload_0" + "\n";
        return commands;
    }

    @Override
    public String visit(ListValue listValue) {
        String commands = "";
        commands += "new List\n";
        commands += "dup\n";

        commands += "new java/util/ArrayList\n";
        commands += "dup\n";
        commands += "invokespecial java/util/ArrayList/<init>()V\n";

        for (Expression element : listValue.getElements()) {
            commands += "dup\n";

            Type exprType = element.accept(expressionTypeChecker);
            if (exprType instanceof IntType) {
                commands += "new java/lang/Integer\n";
                commands += "dup\n";
                commands += element.accept(this);
                commands += "invokespecial java/lang/Integer/<init>(I)V\n";
            }
            else if (exprType instanceof BoolType) {
                commands += "new java/lang/Boolean\n";
                commands += "dup\n";
                commands += element.accept(this);
                commands += "invokespecial java/lang/Boolean/<init>(Z)V\n";
            }
            else {
                commands += element.accept(this);
            }
            commands += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n";
            commands += "pop\n";
        }

        commands += "invokespecial List/<init>(Ljava/util/ArrayList;)V\n";
        return commands;
    }

    @Override
    public String visit(NullValue nullValue) {
        String commands = "";
        commands += "aconst_null\n";
        return commands;
    }

    @Override
    public String visit(IntValue intValue) {
        String commands = "";
        commands += "ldc " + intValue.getConstant() + "\n";
        return commands;
    }

    @Override
    public String visit(BoolValue boolValue) {
        String commands = "";
        if (boolValue.getConstant())
            commands += "ldc 1\n";
        else
            commands += "ldc 0\n";
        return commands;
    }

    @Override
    public String visit(StringValue stringValue) {
        String commands = "";
        commands += "ldc \"" + stringValue.getConstant() + "\"\n";
        return commands;
    }

}