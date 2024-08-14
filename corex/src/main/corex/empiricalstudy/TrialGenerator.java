package corex.empiricalstudy;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Scanner;
import java.util.concurrent.TimeUnit;

import corex.SimulationFailException;
import corex.StepChangeType;
import corex.StepChangeTypeChecker;
import corex.dualSlicingWithConfigE;
import corex.empiricalstudy.RootCauseFinder.TraceNodeW;
import corex.empiricalstudy.solutionpattern.PatternIdentifier;
import corex.handler.PathConfiguration;
import corex.io.RegressionRecorder;
import corex.model.PairList;
import corex.model.StepOperationTuple;
import corex.preference.CorexPreference;
import corex.separatesnapshots.AppClassPathInitializer;
import corex.separatesnapshots.DiffMatcher;
import corex.separatesnapshots.RunningResult;
import corex.separatesnapshots.TraceCollector0;
import corex.tracematch.ControlPathBasedTraceMatcher;
import corex.views.Visualizer;
import microbat.Activator;
import microbat.codeanalysis.runtime.StepLimitException;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.value.VarValue;
import microbat.preference.AnalysisScopePreference;
import microbat.recommendation.DebugState;
import microbat.recommendation.UserFeedback;
import microbat.util.Settings;
import sav.common.core.Pair;
import sav.common.core.utils.SingleTimer;
import sav.strategies.dto.AppJavaClassPath;
import corex.empiricalstudy.Defects4jProjectConfig;
import corex.empiricalstudy.TestCase;

public class TrialGenerator {
	public static final int NORMAL = 0;
	public static final int OVER_LONG = 1;
	public static final int MULTI_THREAD = 2;
	public static final int INSUFFICIENT_TRACE = 3;
	public static final int SAME_LENGTH = 4;
	public static final int OVER_LONG_INSTRUMENTATION_METHOD = 5;
	public static final int EXPECTED_STEP_NOT_MET = 6;
	public static final int UNDETERMINISTIC = 7;

	private RunningResult cachedBuggyRS;
	private RunningResult cachedCorrectRS;

	private DiffMatcher cachedDiffMatcher;
	private PairList cachedPairList;

	public static String getProblemType(int type) {
		switch (type) {
		case OVER_LONG:
			return "some trace is over long";
		case MULTI_THREAD:
			return "it's a multi-thread program";
		case INSUFFICIENT_TRACE:
			return "the trace is insufficient";
		case SAME_LENGTH:
			return "two traces are of the same length";
		case OVER_LONG_INSTRUMENTATION_METHOD:
			return "over long instrumented byte code method";
		case EXPECTED_STEP_NOT_MET:
			return "expected steps are not met";
		case UNDETERMINISTIC:
			return "this is undeterministic testcase";
		default:
			break;
		}
		return "I don't know";
	}
	


//////////////////////////////////////////////////////////////////
	private TraceNode getAssertionNode(Trace newTrace, TestCase tc, String assertionLineNo) {
		for (TraceNode node: newTrace.executionList) {
			String ClassName = node.toString().split("~")[1].split(":")[0];
			String LineNo = node.toString().split("line ")[1].split(" ")[0];
			if (tc.testClass.equals(ClassName) && assertionLineNo.equals(LineNo)) {
				return node;
			}
		}
		return null;
	}
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////
	public void generateTrials(String basePath, String projectName, String bugID, String proPath, String buggyPath, String fixPath, 
			boolean isReuse, boolean useSliceBreaker,
			boolean enableRandom, int breakLimit, boolean requireVisualization, 
			boolean allowMultiThread, Defects4jProjectConfig config, String testcase, List<String> includedClassNames, List<String> excludedClassNames, String eraseorDual, boolean debug, String tool2Run) {
		SingleTimer timer = SingleTimer.start("generateTrial");
		List<TestCase> tcList;
		EmpiricalTrial trial = null;
		TestCase workingTC = null;
		try {

			tcList = retrieveD4jFailingTestCase(buggyPath);
			
			if(testcase!=null){
				tcList = filterSpecificTestCase(testcase, tcList);
			}
			
			for (TestCase tc : tcList) {
				System.out.println("#####working on test case " + tc.testClass + "#" + tc.testMethod);
				workingTC = tc;
				 
				analyzeTestCase(basePath, projectName, bugID, proPath, buggyPath, fixPath, isReuse, allowMultiThread,tc, 
						config, requireVisualization, true, useSliceBreaker, enableRandom, breakLimit, 
						includedClassNames, excludedClassNames, eraseorDual,debug, tool2Run);
			   
//				if(!trial.isDump()){
//					break;					
//				}
			}

		} catch (Exception e) {
			e.printStackTrace();
		}

//		if (trial == null) {
//			trial = EmpiricalTrial.createDumpTrial("runtime exception occurs");
//			trial.setTestcase(workingTC.testClass + "::" + workingTC.testMethod);
//		}
//		trial.setExecutionTime(timer.getExecutionTime());
	}
/////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////
	private List<TestCase> filterSpecificTestCase(String testcase, List<TestCase> tcList) {
		List<TestCase> filteredList = new ArrayList<>();
		for(TestCase tc: tcList){
			String tcName = tc.testClass + "#" + tc.testMethod;
			if(tcName.equals(testcase)){
				filteredList.add(tc);
			}
		}
		
		if(filteredList.isEmpty()){
			filteredList = tcList;
		}
		
		return filteredList;
	}

	private void recompileD4J(String workingPath, Defects4jProjectConfig config) {
		File pathToExecutable = new File(config.rootPath);
		ProcessBuilder builder = new ProcessBuilder(pathToExecutable.getAbsolutePath(), "compile");
		builder.directory(new File(workingPath).getAbsoluteFile() ); // this is where you set the root folder for the executable to run with
		builder.redirectErrorStream(true);
		Process process;
		try {
			process = builder.start();
			Scanner s = new Scanner(process.getInputStream());
			StringBuilder text = new StringBuilder();
			while (s.hasNextLine()) {
				text.append(s.nextLine());
				text.append("\n");
			}
			s.close();
			
			int result = process.waitFor();
			
			System.out.printf( "Process exited with result %d and output %s%n", result, text );
		} catch (IOException | InterruptedException e) {
			e.printStackTrace();
		}

		
	}

	private void generateMainMethod(String workingPath, TestCase tc, Defects4jProjectConfig config) {
		MainMethodGenerator generator = new MainMethodGenerator();
		AppJavaClassPath appCP = AppClassPathInitializer.initialize(workingPath, tc, config);
		String relativePath = tc.testClass.replace(".", File.separator) + ".java";
		String sourcePath = appCP.getTestCodePath() + File.separator + relativePath;
		
		generator.generateMainMethod(sourcePath, tc);
		System.currentTimeMillis();
	}
	
	private EmpiricalTrial analyzeTestCase(String basePath, String projectName, String bugID, String proPath, String buggyPath, String fixPath, 
			boolean isReuse, boolean allowMultiThread, 
			TestCase tc, Defects4jProjectConfig config, boolean requireVisualization, 
			boolean isRunInTestCaseMode, boolean useSliceBreaker, boolean enableRandom, int breakLimit, List<String> includedClassNames, 
			List<String> excludedClassNames, String eraseorDual,boolean debug, String tool2Run) throws SimulationFailException, Exception{
		TraceCollector0 newCollector = new TraceCollector0(true);
		TraceCollector0 oldCollector = new TraceCollector0(false);
		long time1 = 0;
		long time2 = 0;

		RunningResult newRS = null;
		RunningResult oldRs = null;

		DiffMatcher diffMatcher = null;
//		ChangeExtractor diffMatcher = null;
		PairList pairList = null;
        
			Long new_trace_start_time = System.currentTimeMillis();
			try {
				newRS = newCollector.run(buggyPath, tc, config, isRunInTestCaseMode, allowMultiThread, includedClassNames, excludedClassNames);
			} catch (StepLimitException e) {
				if(e.StepLenth == -100) {
//					saveUndeterministicBugAndTerminate(basePath,projectName, bugID);
					System.exit(0);			
				}
				else if (e.StepLenth == -200) {
//					saveMultiThreadBugAndTerminate(basePath,projectName, bugID);
//					System.exit(0);			
				}
				else {
//					saveBugAndTerminate(basePath,projectName, bugID,0,e.StepLenth);
					System.exit(0);			
				}
				
			}		
			if (newRS.getRunningType() != NORMAL) {
				System.out.println("Not normal");
			}
			Long new_trace_finish_time = System.currentTimeMillis();
			int newTraceTime = (int) (new_trace_finish_time - new_trace_start_time);
			
			Long old_trace_start_time = System.currentTimeMillis();
			try {
				oldRs = oldCollector.run(fixPath, tc, config, isRunInTestCaseMode, allowMultiThread, includedClassNames, excludedClassNames);			
			} catch (StepLimitException e) {
				if(e.StepLenth == -100) {
//					saveUndeterministicBugAndTerminate(basePath,projectName, bugID);
					System.exit(0);			
				}
				else if (e.StepLenth == -200) {
//					saveMultiThreadBugAndTerminate(basePath,projectName, bugID);
//					System.exit(0);			
				}
				else {
//					saveBugAndTerminate(basePath,projectName, bugID,oldRs.getRunningTrace().size(),newRS.getRunningTrace().size());	
					System.exit(0);
				}
					
			}
			if (oldRs.getRunningType() != NORMAL) {
				System.out.println("Not normal");
			}
			Long old_trace_finish_time = System.currentTimeMillis();
			int oldTraceTime = (int) (old_trace_finish_time - old_trace_start_time);
			
			int codeTime = 0;
			int traceTime = 0;
			/////////////////////code and trace comparison
			if (newRS != null && oldRs != null) {
					cachedBuggyRS = newRS;
					cachedCorrectRS = oldRs;
					
					//#####################################################
					
					System.out.println("#################################");
					SaveTrace(newRS,oldRs,proPath);
					//#####################################################
					System.out.println("start matching trace..., new trace length: " + newRS.getRunningTrace().size() + ", old trace length: " + oldRs.getRunningTrace().size());		
					System.out.println("#################################");
					long code_match_start_time = System.currentTimeMillis();
					System.out.println("Code Alignement");
					diffMatcher = new DiffMatcher(config.srcSourceFolder, config.srcTestFolder, buggyPath, fixPath);			
					diffMatcher.matchCode();
//					diffMatcher =  new ChangeExtractor(config.srcSourceFolder, config.srcTestFolder, buggyPath, fixPath);
//					diffMatcher.matchCode();
					long code_match_finish_time = System.currentTimeMillis();
					codeTime = (int) (code_match_finish_time - code_match_start_time);
					
					System.out.println("#################################");
					System.out.println("Trace Alignement");
					long trace_match_start_time = System.currentTimeMillis();
					ControlPathBasedTraceMatcher traceMatcher = new ControlPathBasedTraceMatcher();
					if (projectName.contentEquals("InPreSS"))
						pairList = traceMatcher.matchTraceNodePair(newRS.getRunningTrace(), oldRs.getRunningTrace(), diffMatcher,"dual");
					else
						pairList = traceMatcher.matchTraceNodePair(newRS.getRunningTrace(), oldRs.getRunningTrace(), diffMatcher,"inPreSS");
					long trace_match_finish_time = System.currentTimeMillis();					
					traceTime = (int) (trace_match_finish_time - trace_match_start_time);
					System.out.println("finish matching trace, taking " + traceTime + "ms");

//					cachedDiffMatcher = diffMatcher;
//					cachedPairList = pairList;
				}
				
				//////////////////////////dual slicing
				Trace newTrace = newRS.getRunningTrace();
				Trace oldTrace = oldRs.getRunningTrace();
				
				
				System.out.println("#################################");
				RootCauseFinder rootcauseFinder = new RootCauseFinder();
				rootcauseFinder.setRootCauseBasedOnDefects4J(pairList, diffMatcher, newTrace, oldTrace);
				System.out.println("debug: after rootCause (changes)");
				System.out.println("debug: size (changes): " +rootcauseFinder.getRealRootCaseList().size());
				System.out.println("debug: list (changes): " +rootcauseFinder.getRealRootCaseList());
				
				System.out.println("#################################");
				Simulator simulator = new Simulator(useSliceBreaker, enableRandom, breakLimit);
				simulator.prepare(newTrace, oldTrace, pairList, diffMatcher);//parents in getObservedFault
				TraceNode observedFaultNode = simulator.getObservedFault();
				
				dualSlicingWithConfigE configE = new dualSlicingWithConfigE();
				
				Pair<Pair<List<TraceNode>,Pair<HashMap<TraceNode, List<Pair<TraceNode, VarValue>>>,HashMap<TraceNode, List<TraceNode>>>>,Pair<List<TraceNode>,Pair<HashMap<TraceNode, List<Pair<TraceNode, VarValue>>>,HashMap<TraceNode, List<TraceNode>>>>> result = 
						configE.corex(tool2Run,basePath,projectName, bugID,tc, true,proPath,observedFaultNode, newTrace, oldTrace, pairList, diffMatcher, oldTraceTime, newTraceTime, codeTime, traceTime,rootcauseFinder.getRealRootCaseList(),debug);	
				
				StepChangeTypeChecker typeChecker = new StepChangeTypeChecker(newTrace, oldTrace);
				StepChangeType changeType = typeChecker.getType(observedFaultNode, true, pairList, diffMatcher);
				TraceNode observedFault_old = changeType.getMatchingStep();
				List<TraceNode> old_changed = new ArrayList<>();
				List<TraceNode> new_changed = new ArrayList<>();
				for(RootCauseNode changed_node: rootcauseFinder.getRealRootCaseList()) {
					if (changed_node.isOnBefore())
						new_changed.add(changed_node.getRoot());
					else
						old_changed.add(changed_node.getRoot());
				}
						
				if (requireVisualization) {
					Visualizer visualizer = new Visualizer();
					visualizer.visualize(observedFaultNode,observedFault_old,new_changed,old_changed,newTrace, oldTrace, pairList, diffMatcher, newTrace.getExecutionList(), oldTrace.getExecutionList(),result.second().first(), result.first().first(), result.second().second().first(), result.first().second().first(),result.second().second().second(),result.first().second().second());
				}
										
		return null;
	}
		

	private void SaveTrace(RunningResult buggyRS, RunningResult correctRs, String proPath) {
		PrintWriter writer;
		try {
			writer = new PrintWriter(proPath+"/results/new/Trace.txt", "UTF-8");
			for(int i=0; i<buggyRS.getRunningTrace().size(); i++) {
				TraceNode buggyNode = buggyRS.getRunningTrace().getExecutionList().get(i);
				writer.println(buggyNode.toString());	
			}
			writer.close();
			writer = new PrintWriter(proPath+"/results/old/Trace.txt", "UTF-8");
			for(int i=0; i<correctRs.getRunningTrace().size(); i++) {
				TraceNode fixNode = correctRs.getRunningTrace().getExecutionList().get(i);
				writer.println(fixNode.toString());	
			}
			writer.close();
			
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}

	public class DBRecording implements Runnable{

		EmpiricalTrial trial;
		Trace buggyTrace;
		Trace correctTrace;
		DiffMatcher diffMatcher;
		PairList pairList;
		Defects4jProjectConfig config;
		
		public DBRecording(EmpiricalTrial trial, Trace buggyTrace, Trace correctTrace, DiffMatcher diffMatcher,
				PairList pairList, Defects4jProjectConfig config) {
			super();
			this.trial = trial;
			this.buggyTrace = buggyTrace;
			this.correctTrace = correctTrace;
			this.diffMatcher = diffMatcher;
			this.pairList = pairList;
			this.config = config;
		}



		@Override
		public void run() {
			try {
				new RegressionRecorder().record(trial, buggyTrace, correctTrace, pairList, config.projectName, 
						String.valueOf(config.bugID));
			} catch (SQLException e) {
				e.printStackTrace();
			}	
			
		}
		
	}

	public List<TestCase> retrieveD4jFailingTestCase(String buggyVersionPath) throws IOException {
		return Defects4jProjectConfig.retrieveD4jFailingTestCase(buggyVersionPath);
	}
}
