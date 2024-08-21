package corex.empiricalstudy.solutionpattern.control;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.IfStatement;

import corex.empiricalstudy.DeadEndRecord;
import corex.empiricalstudy.EmpiricalTrial;
import corex.empiricalstudy.RootCauseNode;
import corex.empiricalstudy.solutionpattern.PatternDetector;
import corex.empiricalstudy.solutionpattern.SolutionPattern;
import corex.separatesnapshots.DiffMatcher;
import corex.separatesnapshots.diff.DiffChunk;
import corex.separatesnapshots.diff.FilePairWithDiff;
import corex.separatesnapshots.diff.LineChange;

public class MissingIfBlockBody extends PatternDetector{
	@Override
	public boolean detect(DeadEndRecord deadEndRecord, EmpiricalTrial trial) {
		if(deadEndRecord.getType()==DeadEndRecord.DATA){
			return false;
		}
		
		for(RootCauseNode rootCause: trial.getRootCauseFinder().getRealRootCaseList()){
			if(!rootCause.isOnBefore()){
				DiffMatcher matcher = trial.getDiffMatcher();
				for(FilePairWithDiff fileDiff: matcher.getFileDiffList()){
					for(DiffChunk chunk: fileDiff.getChunks()){
						boolean ifBlockFound = isIfBlockFound(chunk, rootCause.getRoot().getLineNumber());
						if(ifBlockFound){
							return true;
						}
					}
				}
			}
		}
		
		return false;
	}

	public class IfBlockFinder extends ASTVisitor{
		
		boolean isFound = false;
		
		@Override
		public boolean visit(IfStatement state){
			isFound = true;
			return false;
		}
	}
	
	private boolean isIfBlockFound(DiffChunk chunk, int lineNumber) {
		StringBuffer buffer = new StringBuffer();
		boolean isHit = false;
		
		
		for(LineChange lineChange: chunk.getChangeList()){
			if(lineChange.getType()==LineChange.ADD){
				String content = lineChange.getLineContent();
				if(content.length()>1){
					buffer.append(content.substring(1, content.length())+"\n");
					
					int line = chunk.getLineNumberInTarget(lineChange);
					if(line==lineNumber){
						isHit = true;
					}
				}
			}
			
		}
		
		if(isHit){
			String code = buffer.toString();
			return code.contains("if") || 
					code.contains("while") || 
					code.contains("for");
		}
		
		return false;
	}

	@Override
	public SolutionPattern getSolutionPattern() {
		return new SolutionPattern(SolutionPattern.MISSING_IF_BLOCK);
	}
}
