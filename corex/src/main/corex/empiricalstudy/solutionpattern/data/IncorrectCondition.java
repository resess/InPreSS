package corex.empiricalstudy.solutionpattern.data;

import java.util.ArrayList;
import java.util.List;

import corex.empiricalstudy.DeadEndRecord;
import corex.empiricalstudy.EmpiricalTrial;
import corex.empiricalstudy.RootCauseNode;
import corex.empiricalstudy.solutionpattern.PatternDetector;
import corex.empiricalstudy.solutionpattern.SolutionPattern;
import corex.separatesnapshots.DiffMatcher;
import corex.separatesnapshots.diff.DiffChunk;
import corex.separatesnapshots.diff.FilePairWithDiff;
import corex.separatesnapshots.diff.LineChange;

public class IncorrectCondition extends PatternDetector{

	@Override
	public boolean detect(DeadEndRecord deadEndRecord, EmpiricalTrial trial) {
		if(deadEndRecord.getType()==DeadEndRecord.CONTROL){
			return false;
		}
		
		for(RootCauseNode rootCause: trial.getRootCauseFinder().getRealRootCaseList()){
			if(rootCause.isOnBefore()){
				DiffMatcher matcher = trial.getDiffMatcher();
				for(FilePairWithDiff filePair: matcher.getFileDiffList()){
					for(DiffChunk chunk: filePair.getChunks()){
						boolean ifChanged = isIfChanged(chunk, filePair);
						if(ifChanged){
							return true;
						}
					}
				}
			}
		}
		
		
		return false;
	}

	private boolean isIfChanged(DiffChunk chunk, FilePairWithDiff filePair) {
		StringBuffer buffer = new StringBuffer();
		List<Integer> removedIfs = new ArrayList<>();
		List<Integer> addedIfs = new ArrayList<>();
		for(LineChange lineChange: chunk.getChangeList()){
			if(lineChange.getType()==LineChange.REMOVE){
				String content = lineChange.getLineContent();
				buffer.append(content.substring(1, content.length())+"\n");
				
				if(content.contains("if")){
					int line = chunk.getLineNumberInSource(lineChange);
					removedIfs.add(line);
				}
			}
			
			if(lineChange.getType()==LineChange.ADD){
				String content = lineChange.getLineContent();
				buffer.append(content.substring(1, content.length())+"\n");
				if(content.contains("if")){
					int line = chunk.getLineNumberInTarget(lineChange);
					addedIfs.add(line);
				}
			}
		}
		System.currentTimeMillis();
		if(!removedIfs.isEmpty() && !addedIfs.isEmpty()){
			for(Integer removedLine: removedIfs){
				for(Integer addedLine: addedIfs){
					List<Integer> targetLines = filePair.getSourceToTargetMap().get(removedLine);
					if(targetLines!=null && targetLines.contains(addedLine)){
						return true;
					}
				}
			}
		}
		
		return false;
	}

	@Override
	public SolutionPattern getSolutionPattern() {
		return new SolutionPattern(SolutionPattern.INCORRECT_CONDITION);
	}
	
}
