package microbat.util;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.GotoInstruction;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.JsrInstruction;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.Select;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdi.TimeoutException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.AbstractTypeDeclaration;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.MethodInvocation;
import org.eclipse.jdt.internal.core.JarPackageFragmentRoot;

import com.sun.jdi.ArrayReference;
import com.sun.jdi.ClassNotLoadedException;
import com.sun.jdi.ClassType;
import com.sun.jdi.Field;
import com.sun.jdi.IncompatibleThreadStateException;
import com.sun.jdi.InvalidTypeException;
import com.sun.jdi.InvocationException;
import com.sun.jdi.Method;
import com.sun.jdi.ObjectReference;
import com.sun.jdi.ReferenceType;
import com.sun.jdi.StackFrame;
import com.sun.jdi.StringReference;
import com.sun.jdi.ThreadReference;
import com.sun.jdi.Value;

import microbat.codeanalysis.ast.MethodDeclarationFinder;
import microbat.codeanalysis.ast.MethodInvocationFinder;
import microbat.codeanalysis.runtime.ProgramExecutor;
import microbat.codeanalysis.runtime.herustic.HeuristicIgnoringFieldRule;
import microbat.codeanalysis.runtime.jpda.expr.ExpressionParser;
import microbat.codeanalysis.runtime.jpda.expr.ParseException;
import microbat.model.trace.TraceNode;
import sav.strategies.dto.AppJavaClassPath;

@SuppressWarnings("restriction")
public class JavaUtil {
	private static final String TO_STRING_SIGN= "()Ljava/lang/String;";
	private static final String TO_STRING_NAME= "toString";
	
	public static boolean isNonJumpInstruction(Instruction ins){
		return !(ins instanceof GotoInstruction) && !(ins instanceof ReturnInstruction) && !(ins instanceof ATHROW) &&
				!(ins instanceof JsrInstruction) && !(ins instanceof Select);
	}
	
	@SuppressWarnings({ "rawtypes", "deprecation" })
	public static CompilationUnit parseCompilationUnit(String file){
		ASTParser parser = ASTParser.newParser(AST.JLS4);
		Map options = JavaCore.getOptions();
		JavaCore.setComplianceOptions(JavaCore.VERSION_1_7, options);
		parser.setCompilerOptions(options);
		parser.setKind(ASTParser.K_COMPILATION_UNIT);
		parser.setResolveBindings(false);
		
		try {
			String text = new String(Files.readAllBytes(Paths.get(file)), StandardCharsets.UTF_8);
			
			parser.setSource(text.toCharArray());
			
			CompilationUnit cu = (CompilationUnit) parser.createAST(null);
			return cu;
			
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return null;
		
	}
	
	public static String retrieveStringValueOfArray(ArrayReference arrayValue) {
		String stringValue;
		List<Value> list = new ArrayList<>();
		if(arrayValue.length() > 0){
			list = arrayValue.getValues(0, arrayValue.length()); 
		}
		StringBuffer buffer = new StringBuffer();
		for(Value v: list){
			String valueString = (v != null) ? v.toString() : "\"null\"";
			buffer.append(valueString);
			buffer.append(",");
		}
		stringValue = buffer.toString();
		return stringValue;
	}
	
	public synchronized static String toPrimitiveValue(ClassType type, ObjectReference value,
			ThreadReference thread) {
		Method method = type.concreteMethodByName(TO_STRING_NAME, TO_STRING_SIGN);
		if (method != null) {
			try {
				if (thread.isSuspended()) {
					if (value instanceof StringReference) {
						return ((StringReference) value).value();
					}
					Field field = type.fieldByName("value");
					Value toStringValue = value.getValue(field);
//					Value toStringValue = value.invokeMethod(thread, method,
//							new ArrayList<Value>(),
//							ObjectReference.INVOKE_SINGLE_THREADED);
					return toStringValue.toString();
					
				}
			} catch (Exception e) {
			}
		}
		return null;
	}
	
	public static String retrieveToStringValue(ObjectReference objValue, int retrieveLayer, ThreadReference thread){
		retrieveLayer--;
		
		ClassType type = (ClassType)objValue.type();
		String typeName = type.name();
		
		if(PrimitiveUtils.isPrimitiveType(typeName)){
			return toPrimitiveValue(type, objValue, thread);
		}
		else if(PrimitiveUtils.isString(typeName)){
			return objValue.toString();
		}
		
		
		Map<Field, Value> map = objValue.getValues(type.allFields());
		List<Field> fieldList = new ArrayList<>(map.keySet());
		Collections.sort(fieldList, new Comparator<Field>() {
			@Override
			public int compare(Field o1, Field o2) {
				return o1.name().compareTo(o2.name());
			}
		});
		
		boolean needParseFields = HeuristicIgnoringFieldRule.isNeedParsingFields(type);
		if(!needParseFields){
			retrieveLayer=1;
		}
		
		StringBuffer buffer = new StringBuffer();
		buffer.append("[");
		for(Field field: fieldList){
			boolean isIgnore = HeuristicIgnoringFieldRule.isForIgnore(type, field);
			if(!isIgnore){
				try {
					String fieldType = field.type().name();
					Value fieldValue = map.get(field);
					
					String fieldValueString = "$unknown";
					if(fieldValue == null){
						fieldValueString = "null";
					}
					else if(PrimitiveUtils.isPrimitiveTypeOrString(fieldType)){
						fieldValueString = fieldValue.toString();
					}
					else if(fieldValue instanceof ArrayReference){
						fieldValueString = JavaUtil.retrieveStringValueOfArray((ArrayReference)fieldValue);
					}
					else if(fieldValue instanceof ObjectReference){
						if(retrieveLayer<=1){
							fieldValueString = fieldValue.toString();
						}
						else{
							fieldValueString = retrieveToStringValue((ObjectReference)fieldValue, retrieveLayer, thread);
						}
					}
					String fString = field.name() + "=" + fieldValueString + "; ";
					buffer.append(fString);
					
				} catch (ClassNotLoadedException e) {
					//e.printStackTrace();
				}
				
			}
		}
		buffer.append("]");
		
		return buffer.toString();
	}
	
//	/**
//	 * This method is used to retrieve the toString() value of an object. I deprecate it for it consume too much
//	 * time when constructing the trace model.
//	 * 
//	 * @param thread
//	 * @param objValue
//	 * @param executor
//	 * @return
//	 * @throws TimeoutException
//	 */
//	@Deprecated
//	public static String retrieveToStringValue(ThreadReference thread,
//			ObjectReference objValue, ProgramExecutor executor) throws TimeoutException {
//		
//		ReferenceType type = (ReferenceType) objValue.type();
//		Method method = type.methodsByName(TO_STRING_NAME, TO_STRING_SIGN).get(0);
//		
//		if(type.toString().equals("org.apache.commons.math.exception.NonMonotonousSequenceException")){
//			System.currentTimeMillis();
//		}
//		
//		boolean classPrepare = executor.getClassPrepareRequest().isEnabled();
//		boolean step = executor.getStepRequest(thread).isEnabled();
//		boolean methodEntry = executor.getMethodEntryRequest().isEnabled();
//		boolean methodExit = executor.getMethodExitRequset().isEnabled();
//		boolean exception = executor.getExceptionRequest().isEnabled();
//		
//		executor.getClassPrepareRequest().disable();
//		executor.getStepRequest(thread).disable();
//		executor.getMethodEntryRequest().disable();
//		executor.getMethodExitRequset().disable();
//		executor.getExceptionRequest().disable();
//		
//		//((VirtualMachine)thread.virtualMachine()).setRequestTimeout(5000);
//		
//		Value messageValue = null;
//		try {
//			messageValue = objValue.invokeMethod(thread, method, 
//					new ArrayList<Value>(), ObjectReference.INVOKE_SINGLE_THREADED);
//		} catch (InvalidTypeException | ClassNotLoadedException | IncompatibleThreadStateException
//				| InvocationException e) {
//			//e.printStackTrace();
//		}
//		
//		executor.getClassPrepareRequest().setEnabled(classPrepare);
//		executor.getStepRequest(thread).setEnabled(step);
//		executor.getMethodEntryRequest().setEnabled(methodEntry);;
//		executor.getMethodExitRequset().setEnabled(methodExit);;
//		executor.getExceptionRequest().setEnabled(exception);;
//		
//		String stringValue = (messageValue != null) ? messageValue.toString() : "null";
//		return stringValue;
//	}
	
	public static Value retriveExpression(final StackFrame frame, String expression){
		ExpressionParser.GetFrame frameGetter = new ExpressionParser.GetFrame() {
            @Override
            public StackFrame get()
                throws IncompatibleThreadStateException
            {
            	return frame;
                
            }
        };
        
        try {
        	
        	Value val = ExpressionParser.evaluate(expression, frame.virtualMachine(), frameGetter);
        	return val;        		
			
		} catch (ParseException e) {
			//e.printStackTrace();
		} catch (InvocationException e) {
			e.printStackTrace();
		} catch (InvalidTypeException e) {
			e.printStackTrace();
		} catch (ClassNotLoadedException e) {
			e.printStackTrace();
		} catch (IncompatibleThreadStateException e) {
			e.printStackTrace();
		} catch (Exception e){
			System.out.println("Cannot parse " + expression);
			e.printStackTrace();
		}
        
        return null;
	}
	
	/**
	 * generate signature such as methodName(java.lang.String)L
	 * @param md
	 * @return
	 */
	public static String generateMethodSignature(IMethodBinding mBinding){
//		IMethodBinding mBinding = md.resolveBinding();
		
		String returnType = mBinding.getReturnType().getKey();
		
		String methodName = mBinding.getName();
		
		List<String> paramTypes = new ArrayList<>();
		for(ITypeBinding tBinding: mBinding.getParameterTypes()){
			String paramType = tBinding.getKey();
			paramTypes.add(paramType);
		}
		
		StringBuffer buffer = new StringBuffer();
		buffer.append(methodName);
		buffer.append("(");
		for(String pType: paramTypes){
			buffer.append(pType);
			//buffer.append(";");
		}
		
		buffer.append(")");
		buffer.append(returnType);
//		
//		String sign = buffer.toString();
//		if(sign.contains(";")){
//			sign = sign.substring(0, sign.lastIndexOf(";")-1);			
//		}
//		sign = sign + ")" + returnType;
		
		String sign = buffer.toString();
		
		return sign;
	}
	
	public static String getFullNameOfCompilationUnit(CompilationUnit cu){
		
		String packageName = "";
		if(cu.getPackage() != null){
			packageName = cu.getPackage().getName().toString();
		}
		//System.out.println("package Name: " + packageName);
		if(cu.types().size()!=0) {
			AbstractTypeDeclaration typeDeclaration = (AbstractTypeDeclaration) cu.types().get(0);
			String typeName = typeDeclaration.getName().getIdentifier();
			//System.out.println("type Name: " + typeName);
			
			if(packageName.length() == 0){
				return typeName;
			}
			else{
				return packageName + "." + typeName; 			
			}
		}
		else {
			return "null";
		}
		
	}
	
	
	public static CompilationUnit findCompilationUnitInProject(String qualifiedName, AppJavaClassPath appPath){
		CompilationUnit cu = Settings.compilationUnitMap.get(qualifiedName);
		if(null == cu){
			try{
				ICompilationUnit icu = findICompilationUnitInProject(qualifiedName);
				if(icu != null){
					cu = convertICompilationUnitToASTNode(icu);						
				}
				else{
					
					boolean isFound = false;
					for(String sourceFolder: appPath.getAllSourceFolders()){
						String fileName = sourceFolder + File.separator + qualifiedName.replace(".", File.separator) + ".java";
						if(new File(fileName).exists()){
							cu = findCompiltionUnitBySourcePath(fileName, qualifiedName);
							isFound = true;
							break;
						}
					}
					
					if(!isFound){
						System.err.println("cannot find the source file of " + qualifiedName);
					}
					
//					String sourceFile = appPath.getSoureCodePath() + File.separator + qualifiedName.replace(".", File.separator) + ".java";
//					String testFile = appPath.getTestCodePath() + File.separator + qualifiedName.replace(".", File.separator) + ".java";
//					
//					if(new File(sourceFile).exists()) {
//						cu = findCompiltionUnitBySourcePath(sourceFile, qualifiedName);
//					}
//					else if(new File(testFile).exists()) {
//						cu = findCompiltionUnitBySourcePath(testFile, qualifiedName);
//					}
//					else {
//						System.err.println("cannot find the source file of " + qualifiedName);
//					}
					
				}
				
				Settings.compilationUnitMap.put(qualifiedName, cu);
				return cu;
			}
			catch(IllegalStateException e){
				e.printStackTrace();
			} 
		}
		
		return cu;
	} 
	
	public static CompilationUnit findNonCacheCompilationUnitInProject(String qualifiedName, AppJavaClassPath appPath){
		ICompilationUnit icu = findNonCacheICompilationUnitInProject(qualifiedName);
		CompilationUnit cu = null;
		if(icu != null){
			cu = convertICompilationUnitToASTNode(icu);						
		}
		else{
			String sourceFile = appPath.getSoureCodePath() + File.separator + qualifiedName.replace(".", File.separator) + ".java";
			String testFile = appPath.getTestCodePath() + File.separator + qualifiedName.replace(".", File.separator) + ".java";
			
			if(new File(sourceFile).exists()) {
				cu = findCompiltionUnitBySourcePath(sourceFile, qualifiedName);
			}
			else if(new File(testFile).exists()) {
				cu = findCompiltionUnitBySourcePath(testFile, qualifiedName);
			}
			else {
				System.err.println("cannot find the source file of " + qualifiedName);
			}
		}
		
		return cu;
	}
	
	public static ICompilationUnit findICompilationUnitInProject(String qualifiedName) {
		return findICompilationUnitInProject(qualifiedName, Settings.projectName);
	}
	
	public static ICompilationUnit findICompilationUnitInProject(String qualifiedName, String projectName){
		//System.out.println("qualifiedName: " + qualifiedName);
		ICompilationUnit icu = Settings.iCompilationUnitMap.get(qualifiedName);
		
		
//		if(icu == null){
//			IProject iProject = getSpecificJavaProjectInWorkspace(projectName);
//			if(iProject != null){
//				System.out.println("iProject is not null");
//				IJavaProject project = JavaCore.create(iProject);
//				try {
//					IType type = project.findType(qualifiedName);
//					if(type == null){
//						type = project.findType(qualifiedName, new NullProgressMonitor());
//					}
//					
//					if(type != null){
//						icu = type.getCompilationUnit();
//						Settings.iCompilationUnitMap.put(qualifiedName, icu);
//					}
//					
//				} catch (JavaModelException e1) {
//					//System.out.println(e1);
//				}
//			}
//		}
		
		return icu;
	}
	
	public static ICompilationUnit findNonCacheICompilationUnitInProject(String qualifiedName) {
		return findNonCacheICompilationUnitInProject(qualifiedName, Settings.projectName);
	}
	
	public static ICompilationUnit findNonCacheICompilationUnitInProject(String qualifiedName, String projectName) {
		IProject iProject = getSpecificJavaProjectInWorkspace(projectName);
		if(iProject != null){
			IJavaProject project = JavaCore.create(iProject);
			try {
				IType type = project.findType(qualifiedName);
				if(type != null){
					return  type.getCompilationUnit();
				}
				
			} catch (JavaModelException e1) {
				e1.printStackTrace();
			}
			
		}
		
		return null;
	}
	
	public static IPackageFragmentRoot findTestPackageRootInProject(){
		return findTestPackageRootInProject(Settings.projectName);
	}
	
	public static IPackageFragmentRoot findTestPackageRootInProject(String projectName){
		IJavaProject project = JavaCore.create(getSpecificJavaProjectInWorkspace(projectName));
		try {
			for(IPackageFragmentRoot packageFragmentRoot: project.getPackageFragmentRoots()){
				if(!(packageFragmentRoot instanceof JarPackageFragmentRoot) && packageFragmentRoot.getResource().toString().contains("test")){
					
					return packageFragmentRoot;
//					IPackageFragment packageFrag = packageFragmentRoot.getPackageFragment(packageName);
//					
//					String fragName = packageFrag.getElementName();
//					if(packageFrag.exists() && fragName.equals(packageName)){
//						return packageFrag;
//					}
					
				}
			}
			
		} catch (JavaModelException e1) {
			e1.printStackTrace();
		}
		
		return null;
	}
	
	@SuppressWarnings({ "rawtypes", "deprecation" })
	public static CompilationUnit convertICompilationUnitToASTNode(ICompilationUnit iunit){
		ASTParser parser = ASTParser.newParser(AST.JLS4);
		Map options = JavaCore.getOptions();
		JavaCore.setComplianceOptions(JavaCore.VERSION_1_7, options);
		parser.setCompilerOptions(options);
		parser.setKind(ASTParser.K_COMPILATION_UNIT);
		parser.setResolveBindings(true);
		parser.setSource(iunit);
		
		CompilationUnit cu = null;
		try{
			cu = (CompilationUnit) parser.createAST(null);		
			return cu;
		}
		catch(java.lang.IllegalStateException e){
			return null;
		}
	}
	
	public static IProject getSpecificJavaProjectInWorkspace(){
		return getSpecificJavaProjectInWorkspace(Settings.projectName);
	}
	
	public static IProject getSpecificJavaProjectInWorkspace(String projectName){
		System.out.println("the project is empty" +projectName);
		IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IWorkspaceRoot root = workspace.getRoot();
		IProject[] projects = root.getProjects();
		
		for(int i=0; i<projects.length; i++){
			if(projects[i].getName().equals(projectName)){
				System.out.println("project is return");
				return projects[i];
			}
		}
		System.out.println("project is null");
		return null;
	}

	public static boolean isTheLocationHeadOfClass(String sourceName, int lineNumber, AppJavaClassPath appPath) {
		CompilationUnit cu = findCompilationUnitInProject(sourceName, appPath);
		AbstractTypeDeclaration type = (AbstractTypeDeclaration) cu.types().get(0);
		int headLine = cu.getLineNumber(type.getName().getStartPosition());
		
		return headLine==lineNumber;
	}

	public static boolean isCompatibleMethodSignature(String thisSig, String thatSig, AppJavaClassPath appPath) {
		if(thatSig.equals(thisSig)){
			return true;
		}
		
		String thisClassName = thisSig.substring(0, thisSig.indexOf("#"));
		String thisMethodSig = thisSig.substring(thisSig.indexOf("#")+1, thisSig.length());
		
		String thatClassName = thatSig.substring(0, thatSig.indexOf("#"));
		String thatMethodSig = thatSig.substring(thatSig.indexOf("#")+1, thatSig.length());
		
		if(thisMethodSig.equals(thatMethodSig)){
			CompilationUnit thisCU = JavaUtil.findCompilationUnitInProject(thisClassName, appPath);
			CompilationUnit thatCU = JavaUtil.findCompilationUnitInProject(thatClassName, appPath);
			
			if(thisCU==null || thatCU==null){
				return true;
			}
			
			AbstractTypeDeclaration thisType = (AbstractTypeDeclaration) thisCU.types().get(0);
			AbstractTypeDeclaration thatType = (AbstractTypeDeclaration) thatCU.types().get(0);
			
			ITypeBinding thisTypeBinding = thisType.resolveBinding();
			ITypeBinding thatTypeBinding = thatType.resolveBinding();
			
			boolean isSame = thisTypeBinding.getQualifiedName().equals(thatTypeBinding.getQualifiedName());
			
			if(isSame){
				return true;
			}
			else{
				boolean isCom1 = thisTypeBinding.isSubTypeCompatible(thatTypeBinding);
				boolean isCom2 = thatTypeBinding.isSubTypeCompatible(thisTypeBinding);
				
				return isCom1 || isCom2;				
			}
		}
		
		return false;
	}
	
	/**
	 * If the prevNode is the invocation parent of postNode, this method return the method binding of the
	 * corresponding method.
	 *  
	 * @param prevNode
	 * @param postNode
	 * @return
	 */
	public static MethodDeclaration checkInvocationParentRelation(TraceNode prevNode, TraceNode postNode, AppJavaClassPath appPath){
		List<IMethodBinding> methodInvocationBindings = findMethodInvocations(prevNode, appPath);
		if(!methodInvocationBindings.isEmpty()){
			MethodDeclaration md = findMethodDeclaration(postNode, appPath);
			if(md == null){
				return null;
			}
			IMethodBinding methodDeclarationBinding = md.resolveBinding();
			
			if(canFindCompatibleSig(methodInvocationBindings, methodDeclarationBinding, appPath)){
				//return methodDeclarationBinding;
				return md;
			}
		}
		
		return null;
	}

	private static List<IMethodBinding> findMethodInvocations(TraceNode prevNode, AppJavaClassPath appPath) {
		CompilationUnit cu = JavaUtil.findCompilationUnitInProject(prevNode.getDeclaringCompilationUnitName(), appPath);
		
		MethodInvocationFinder finder = new MethodInvocationFinder(cu, prevNode.getLineNumber());
		cu.accept(finder);
		
		List<IMethodBinding> methodInvocations = new ArrayList<>();
		
		List<MethodInvocation> invocations = finder.getInvocations();
		for(MethodInvocation invocation: invocations){
			IMethodBinding mBinding = invocation.resolveMethodBinding();
			
			methodInvocations.add(mBinding);
			
		}
		
		return methodInvocations;
	}

	private static MethodDeclaration findMethodDeclaration(TraceNode postNode, AppJavaClassPath appPath) {
		CompilationUnit cu = JavaUtil.findCompilationUnitInProject(postNode.getDeclaringCompilationUnitName(), appPath);
		
		MethodDeclarationFinder finder = new MethodDeclarationFinder(cu, postNode.getLineNumber());
		cu.accept(finder);
		
		MethodDeclaration md = finder.getMethod();
		
		
		return md;
	}
	
	public static String convertFullSignature(IMethodBinding binding){
		
		String className = binding.getDeclaringClass().getBinaryName();
		String methodSig = generateMethodSignature(binding);
		
		return className + "#" + methodSig;
	}

	private static boolean canFindCompatibleSig(
			List<IMethodBinding> methodInvocationBindings, IMethodBinding methodDeclarationBinding, AppJavaClassPath appPath) {
		
		List<String> methodInvocationSigs = new ArrayList<>();
		for(IMethodBinding binding: methodInvocationBindings){
			String sig = convertFullSignature(binding);
			methodInvocationSigs.add(sig);
		}
		String methodDeclarationSig = convertFullSignature(methodDeclarationBinding);
		
		if(methodInvocationSigs.contains(methodDeclarationSig)){
			return true;
		}
		else{
			for(String methodInvocationSig: methodInvocationSigs){
				if(isCompatibleMethodSignature(methodInvocationSig, methodDeclarationSig, appPath)){
					return true;
				}
			}
		}
		
		System.currentTimeMillis();
		
		return false;
	}
	
	public static String createSignature(String className, String methodName, String methodSig) {
		String sig = className + "#" + methodName + methodSig;
		return sig;
	}

	public static HashMap<String, CompilationUnit> sourceFile2CUMap = new HashMap<>();
	
	public static CompilationUnit findCompiltionUnitBySourcePath(String javaFilePath, 
			String declaringCompilationUnitName) {
		
		CompilationUnit parsedCU = sourceFile2CUMap.get(javaFilePath);
		if(parsedCU != null) {
			return parsedCU;
		}
		
		File javaFile = new File(javaFilePath);
		
		if(javaFile.exists()){
			
			String contents;
			try {
				contents = new String(Files.readAllBytes(Paths.get(javaFilePath)));
				
				final ASTParser parser = ASTParser.newParser(AST.JLS8);
				parser.setKind(ASTParser.K_COMPILATION_UNIT);
				parser.setSource(contents.toCharArray());
				parser.setResolveBindings(true);
				
				CompilationUnit cu = (CompilationUnit)parser.createAST(null);
				sourceFile2CUMap.put(javaFilePath, cu);
				
				return cu;
				
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		else{
			System.err.print("cannot find " + declaringCompilationUnitName + " under " + javaFilePath);			
		}
		
		return null;
	}
}
