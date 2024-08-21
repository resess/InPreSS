package corex.empiricalstudy.solutionpattern.data;

import corex.StepChangeType;
import corex.StepChangeTypeChecker;
import corex.empiricalstudy.DeadEndRecord;
import corex.empiricalstudy.EmpiricalTrial;
import corex.empiricalstudy.solutionpattern.PatternDetector;
import corex.empiricalstudy.solutionpattern.SolutionPattern;
import corex.model.TraceNodePair;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;

public class MissEvaluedCondition extends PatternDetector {

	@Override
	public boolean detect(DeadEndRecord deadEndRecord, EmpiricalTrial trial) {
		int breakStepOrder = deadEndRecord.getBreakStepOrder();
		Trace buggyTrace = trial.getBuggyTrace();
		
		TraceNode breakStep = buggyTrace.getTraceNode(breakStepOrder);
		
		if(!breakStep.isConditional()){
			return false;
		}
		
		TraceNodePair pair = trial.getPairList().findByBeforeNode(breakStep);
		if(pair != null && pair.getAfterNode()!=null){
			StepChangeTypeChecker checker = new StepChangeTypeChecker(buggyTrace, trial.getFixedTrace());
			StepChangeType diffType = checker.getType(breakStep, true, trial.getPairList(), trial.getDiffMatcher());
			
			if(diffType.getType()==StepChangeType.DAT){
				return true;
			}
		}
		
		return false;
	}

	@Override
	public SolutionPattern getSolutionPattern() {
		return new SolutionPattern(SolutionPattern.MISS_EVALUATED_CONDITION);
	}

}
