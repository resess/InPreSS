package resess;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import tregression.SimulationFailException;
import tregression.empiricalstudy.Defects4jProjectConfig;
import tregression.empiricalstudy.RootCauseFinder;
import tregression.empiricalstudy.Simulator;
import tregression.empiricalstudy.TestCase;
import tregression.model.PairList;
import tregression.separatesnapshots.DiffMatcher;
import tregression.separatesnapshots.RunningResult;
import tregression.separatesnapshots.TraceCollector0;
import tregression.tracematch.ControlPathBasedTraceMatcher;

public class generateResults {
	public static final int NORMAL = 0;
	public static final int OVER_LONG = 1;
	public static final int MULTI_THREAD = 2;
	public static final int INSUFFICIENT_TRACE = 3;
	public static final int SAME_LENGTH = 4;
	public static final int OVER_LONG_INSTRUMENTATION_METHOD = 5;
	public static final int EXPECTED_STEP_NOT_MET = 6;
	public static final int UNDETERMINISTIC = 7;

	public void generateResult(String basePath, String projectName, String bugID, String proPath, String buggyPath, String fixPath, 
			boolean isReuse, boolean useSliceBreaker,
			boolean enableRandom, int breakLimit, boolean requireVisualization, 
			boolean allowMultiThread, Defects4jProjectConfig config, String testcase, List<String> includedClassNames, List<String> excludedClassNames, String eraseorDual, boolean debug) {
		List<TestCase> tcList;
		TestCase workingTC = null;
		try {
			tcList = retrieveD4jFailingTestCase(buggyPath);			
			if(testcase!=null){
				tcList = filterSpecificTestCase(testcase, tcList);
			}			
			for (TestCase tc : tcList) {
				System.out.println("#####working on test case " + tc.testClass + "#" + tc.testMethod);
				workingTC = tc;				 
				analyzeTestCaseResult(basePath, projectName, bugID, proPath, buggyPath, fixPath, isReuse, allowMultiThread,tc, 
						config, requireVisualization, true, useSliceBreaker, enableRandom, breakLimit, 
						includedClassNames, excludedClassNames, eraseorDual,debug);		
			    System.exit(0);
			}

		} catch (Exception e) {
			e.printStackTrace();
		}
	}
    //////////////////////////////////////////////////////////////////	
    private void analyzeTestCaseResult(String basePath, String projectName, String bugID, String proPath, String buggyPath, String fixPath, 
			boolean isReuse, boolean allowMultiThread, 
			TestCase tc, Defects4jProjectConfig config, boolean requireVisualization, 
			boolean isRunInTestCaseMode, boolean useSliceBreaker, boolean enableRandom, int breakLimit, List<String> includedClassNames, 
			List<String> excludedClassNames, String eraseorDual,boolean debug) throws SimulationFailException, IOException {
		TraceCollector0 newCollector = new TraceCollector0(true);
		TraceCollector0 oldCollector = new TraceCollector0(false);


		RunningResult newRS = null;
		RunningResult oldRs = null;

		DiffMatcher diffMatcher = null;
		PairList dualPairList = null;
		PairList inPreSSPairList = null;	


		Long new_trace_start_time = System.currentTimeMillis();
		newRS = newCollector.run(buggyPath, tc, config, isRunInTestCaseMode, allowMultiThread, includedClassNames, excludedClassNames);
		if (newRS.getRunningType() != NORMAL) {
			System.out.println("Not normal");
		}
		Long new_trace_finish_time = System.currentTimeMillis();
		int newTraceTime = (int) (new_trace_finish_time - new_trace_start_time);
		
		Long old_trace_start_time = System.currentTimeMillis();
		oldRs = oldCollector.run(fixPath, tc, config, isRunInTestCaseMode, allowMultiThread, includedClassNames, excludedClassNames);
		if (oldRs.getRunningType() != NORMAL) {
			System.out.println("Not normal");
		}
		Long old_trace_finish_time = System.currentTimeMillis();
		int oldTraceTime = (int) (old_trace_finish_time - old_trace_start_time);
		
		int codeTime = 0;
		int traceTime = 0;
		/////////////////////code and trace comparison
		if (newRS != null && oldRs != null) {
					
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
			long code_match_finish_time = System.currentTimeMillis();
			codeTime = (int) (code_match_finish_time - code_match_start_time);
			
			
			System.out.println("#################################");
			System.out.println("Trace Alignement");
			long trace_match_start_time = System.currentTimeMillis();
			ControlPathBasedTraceMatcher traceMatcher = new ControlPathBasedTraceMatcher();
			dualPairList = traceMatcher.matchTraceNodePair(newRS.getRunningTrace(), oldRs.getRunningTrace(), diffMatcher,"dual");
//			inPreSSPairList = traceMatcher.matchTraceNodePair(newRS.getRunningTrace(), oldRs.getRunningTrace(), diffMatcher,"inPreSS");
			long trace_match_finish_time = System.currentTimeMillis();					
			traceTime = (int) (trace_match_finish_time - trace_match_start_time);
			System.out.println("finish matching trace, taking " + traceTime + "ms");

		}
				
		//////////////////////////dual slicing
		Trace newTrace = newRS.getRunningTrace();
		Trace oldTrace = oldRs.getRunningTrace();
				
		System.out.println("#################################");
		RootCauseFinder rootcauseFinder = new RootCauseFinder();
//		rootcauseFinder.setRootCauseBasedOnDefects4J(inPreSSPairList, diffMatcher, newTrace, oldTrace);
		rootcauseFinder.setRootCauseBasedOnDefects4J(dualPairList, diffMatcher, newTrace, oldTrace);
		
		//////////////////////////
		System.out.println("#################################");
		Simulator simulator = new Simulator(useSliceBreaker, enableRandom, breakLimit);
//		simulator.prepare(newTrace, oldTrace, inPreSSPairList, diffMatcher);//parents in getObservedFault
		simulator.prepare(newTrace, oldTrace, dualPairList, diffMatcher);//parents in getObservedFault
		//System.out.println(simulator.getObservedFault());
		TraceNode observedFaultNode = simulator.getObservedFault();
		
		
		System.out.println("###############Dual slicing##################");
		if (eraseorDual.equals("S")){
			dualSlicingWithConfigS configS = new dualSlicingWithConfigS();
			configS.dualSlicing(basePath,projectName, bugID,tc, true,proPath,observedFaultNode, newTrace, oldTrace, dualPairList, inPreSSPairList, diffMatcher, oldTraceTime, newTraceTime, codeTime, traceTime,rootcauseFinder.getRealRootCaseList(),debug);	
		}
		else if (eraseorDual.equals("E")){
			dualSlicingWithConfigE configE = new dualSlicingWithConfigE();
			configE.dualSlicing(basePath,projectName, bugID,tc, false, proPath, observedFaultNode, newTrace, oldTrace, dualPairList, inPreSSPairList, diffMatcher, oldTraceTime, newTraceTime, codeTime, traceTime,rootcauseFinder.getRealRootCaseList(),debug);
		}
		
		return;
	}
    //////////////////////////////////////////////////////////////////
    private void SaveTrace(RunningResult buggyRS, RunningResult correctRs, String proPath) {
		PrintWriter writer;
		try {
			Path path = Paths.get(proPath+"/results");
			if(!Files.exists(path)) {
				new File(proPath+"/results").mkdirs();
				new File(proPath+"/results/new").mkdirs();
				new File(proPath+"/results/old").mkdirs();
			}
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
	//////////////////////////////////////////////////////////////////	
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
	//////////////////////////////////////////////////////////////////
	public List<TestCase> retrieveD4jFailingTestCase(String buggyVersionPath) throws IOException {
		return Defects4jProjectConfig.retrieveD4jFailingTestCase(buggyVersionPath);
	}

}
