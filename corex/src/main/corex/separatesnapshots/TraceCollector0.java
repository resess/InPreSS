package corex.separatesnapshots;

import java.util.List;

import corex.empiricalstudy.Defects4jProjectConfig;
import corex.empiricalstudy.TestCase;
import corex.empiricalstudy.TrialGenerator;
import microbat.codeanalysis.runtime.InstrumentationExecutor;
import microbat.codeanalysis.runtime.PreCheckInformation;
import microbat.instrumentation.output.RunningInfo;
import microbat.codeanalysis.runtime.StepLimitException;
import microbat.model.trace.Trace;
import microbat.util.MicroBatUtil;
import sav.strategies.dto.AppJavaClassPath;

public class TraceCollector0 {
	private boolean isBuggy;
	
	public TraceCollector0(boolean buggy) {
		this.isBuggy = buggy;
	}
	
	public RunningResult run(String workingDir, TestCase tc, 
			Defects4jProjectConfig config, boolean isRunInTestCaseMode, boolean allowMultiThread, 
			List<String> includeLibs, List<String> excludeLibs) throws StepLimitException{
		
		AppJavaClassPath appClassPath = AppClassPathInitializer.initialize(workingDir, tc, config);
		if(!isRunInTestCaseMode) {
			System.out.println(appClassPath.getOptionalTestClass());
			appClassPath.setLaunchClass(appClassPath.getOptionalTestClass());
		}
		
		String traceDir = MicroBatUtil.generateTraceDir(config.projectName, String.valueOf(config.bugID));
		String traceName = isBuggy ? "bug" : "fix";
		InstrumentationExecutor exectuor = new InstrumentationExecutor(appClassPath,traceDir, traceName, includeLibs, excludeLibs);
		
		RunningInfo info = null;
		try {
			info = exectuor.run(config.projectName,String.valueOf(config.bugID));
		} catch (StepLimitException e) {
//			e.printStackTrace();			
			throw new StepLimitException(e.StepLenth);
		}
		
		PreCheckInformation precheckInfo = exectuor.getPrecheckInfo();
		System.out.println("There are " + precheckInfo.getStepNum() + " steps in this trace");
		if(precheckInfo.isOverLong()) {
			System.out.println("The trace is over long!");
			RunningResult rs = new RunningResult();
			rs.setFailureType(TrialGenerator.OVER_LONG);
			return rs;
		}
		
//		if(!precheckInfo.getOverLongMethods().isEmpty()) {
//			String method = precheckInfo.getOverLongMethods().get(0);
//			System.out.println("Method " + method + " is over long after instrumentation!");
//			RunningResult rs = new RunningResult();
//			rs.setFailureType(TrialGenerator0.OVER_LONG_INSTRUMENTATION_METHOD);
//			return rs;
//		}
		
		if(precheckInfo.isUndeterministic()){
			System.out.println("This is undeterministic testcase!");
			RunningResult rs = new RunningResult();
			rs.setFailureType(TrialGenerator.UNDETERMINISTIC);
			return rs;
		}
		
		
		boolean isMultiThread = precheckInfo.getThreadNum()!=1;
		if(isMultiThread && !allowMultiThread) {
			System.out.println("It is multi-thread program!");
			RunningResult rs = new RunningResult();
			rs.setFailureType(TrialGenerator.MULTI_THREAD);
			return rs;
		}
		
//		if(!info.isExpectedStepsMet()){
//			System.out.println("The expected steps are not met by normal run");
//			RunningResult rs = new RunningResult();
//			rs.setFailureType(TrialGenerator0.EXPECTED_STEP_NOT_MET);
//			return rs;
//		}
		
		Trace trace = info.getMainTrace();
		trace.constructLoopParentRelation();
		trace.setSourceVersion(isBuggy);
		
		RunningResult rs = new RunningResult(trace, null, null, precheckInfo, appClassPath);
		rs.setRunningTrace(trace);
		rs.setRunningInfo(info);
		return rs;
	}
	
}