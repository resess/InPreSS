package corex.empiricalstudy.solutionpattern;

import java.util.ArrayList;
import java.util.List;

import corex.empiricalstudy.DeadEndRecord;
import corex.empiricalstudy.EmpiricalTrial;
import corex.empiricalstudy.solutionpattern.control.InvokeDifferentMethod;
import corex.empiricalstudy.solutionpattern.control.MissingIfBlockBody;
import corex.empiricalstudy.solutionpattern.control.MissingIfReturn;
import corex.empiricalstudy.solutionpattern.control.MissingIfThrow;
import corex.empiricalstudy.solutionpattern.data.ExtraNestedIfBlock;
import corex.empiricalstudy.solutionpattern.data.IncorrectAssignment;
import corex.empiricalstudy.solutionpattern.data.IncorrectCondition;
import corex.empiricalstudy.solutionpattern.data.InvokeNewMethod;
import corex.empiricalstudy.solutionpattern.data.MissEvaluedCondition;
import corex.empiricalstudy.solutionpattern.data.MissingAssignment;

public class PatternIdentifier {
	
	List<PatternDetector> patternDetectors = new ArrayList<>();
	
	public PatternIdentifier(){
		//TODO initialize the pattern detectors
		patternDetectors.add(new MissingIfThrow());
		patternDetectors.add(new MissingIfReturn());
		patternDetectors.add(new IncorrectCondition());
		patternDetectors.add(new MissEvaluedCondition());
		patternDetectors.add(new MissingAssignment());
		patternDetectors.add(new ExtraNestedIfBlock());
		patternDetectors.add(new MissingIfBlockBody());
		patternDetectors.add(new IncorrectAssignment());
		patternDetectors.add(new InvokeDifferentMethod());
		patternDetectors.add(new InvokeNewMethod());
	}
	
	public void identifyPattern(EmpiricalTrial trial){
		for(DeadEndRecord record: trial.getDeadEndRecordList()){
			identifyPattern(record, trial);
		}
	}

	private void identifyPattern(DeadEndRecord record, EmpiricalTrial trial) {
		for(PatternDetector detector: patternDetectors){
			boolean detected = detector.detect(record, trial);
			if(detected){
				record.setSolutionPattern(detector.getSolutionPattern());
				break;
			}
		}
	}
}
