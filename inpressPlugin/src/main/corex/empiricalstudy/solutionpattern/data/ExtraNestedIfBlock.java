package corex.empiricalstudy.solutionpattern.data;

import org.eclipse.jdt.core.dom.ASTNode;
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

public class ExtraNestedIfBlock extends PatternDetector{
	@Override
	public boolean detect(DeadEndRecord deadEndRecord, EmpiricalTrial trial) {
		if(deadEndRecord.getType()==DeadEndRecord.CONTROL){
			return false;
		}
		
//		RootCauseNode rootCause = trial.getRealcauseNode();
		for(RootCauseNode rootCause: trial.getRootCauseFinder().getRealRootCaseList()){
			if(rootCause.isOnBefore()){
				DiffMatcher matcher = trial.getDiffMatcher();
				for(FilePairWithDiff filePair: matcher.getFileDiffList()){
					for(DiffChunk chunk: filePair.getChunks()){
						boolean ifRemoved = isIfRemoved(chunk, rootCause.getRoot().getLineNumber());
						if(ifRemoved){
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
	
	private boolean isIfRemoved(DiffChunk chunk, int lineNumber) {
		StringBuffer buffer = new StringBuffer();
		boolean isHit = false;
		for(LineChange lineChange: chunk.getChangeList()){
			if(lineChange.getType()==LineChange.REMOVE){
				String content = lineChange.getLineContent();
				buffer.append(content.substring(1, content.length())+"\n");
				
				int line = chunk.getLineNumberInSource(lineChange);
				if(line==lineNumber){
					isHit = true;
				}
			}
		}
		
		if(isHit){
			String code = buffer.toString();
			ASTNode node = parseAST(code);
			IfBlockFinder finder = new IfBlockFinder();
			node.accept(finder);
			boolean isFound = finder.isFound;
			return isFound;
		}
		
		return false;
	}

	@Override
	public SolutionPattern getSolutionPattern() {
		return new SolutionPattern(SolutionPattern.EXTRA_NESTED_IF_BLOCK);
	}
}
