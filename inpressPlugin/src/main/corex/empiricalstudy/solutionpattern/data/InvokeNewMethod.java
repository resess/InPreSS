package corex.empiricalstudy.solutionpattern.data;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.MethodInvocation;

import corex.empiricalstudy.DeadEndRecord;
import corex.empiricalstudy.EmpiricalTrial;
import corex.empiricalstudy.RootCauseNode;
import corex.empiricalstudy.solutionpattern.PatternDetector;
import corex.empiricalstudy.solutionpattern.SolutionPattern;
import corex.separatesnapshots.DiffMatcher;
import corex.separatesnapshots.diff.DiffChunk;
import corex.separatesnapshots.diff.FilePairWithDiff;
import corex.separatesnapshots.diff.LineChange;

public class InvokeNewMethod extends PatternDetector{

	@Override
	public boolean detect(DeadEndRecord deadEndRecord, EmpiricalTrial trial) {
		if(deadEndRecord.getType()==DeadEndRecord.CONTROL){
			return false;
		}
		
		for(RootCauseNode rootCause: trial.getRootCauseFinder().getRealRootCaseList()){
			if(!rootCause.isOnBefore()){
				DiffMatcher matcher = trial.getDiffMatcher();
				for(FilePairWithDiff filePair: matcher.getFileDiffList()){
					for(DiffChunk chunk: filePair.getChunks()){
						boolean isNewMethodInvoked = checkMethodInvocation(chunk, filePair);
						if(isNewMethodInvoked){
							return true;
						}
					}
				}
			}
		}
		
		
		return false;
	}
	
	class MethodInvocationFinder extends ASTVisitor{
		boolean isFound = false;
		String methodName;
		
		@Override
		public boolean visit(MethodInvocation invocation){
			isFound = true;
			methodName = invocation.getName().getFullyQualifiedName();
			return false;
		}
	}
	
	private boolean checkMethodInvocation(DiffChunk chunk, FilePairWithDiff filePair) {
		Map<Integer, String> removedInvocations = new HashMap<>();
		Map<Integer, String> addedInvocations = new HashMap<>();
		for(LineChange lineChange: chunk.getChangeList()){
			if(lineChange.getType()==LineChange.REMOVE){
				String content = lineChange.getLineContent();
				content = content.substring(1, content.length());
				
				ASTNode node = parseAST(content);
				MethodInvocationFinder finder = new MethodInvocationFinder();
				node.accept(finder);
				
				if(finder.isFound){
					int line = chunk.getLineNumberInSource(lineChange);
					removedInvocations.put(line, finder.methodName);
				}
			}
			
			if(lineChange.getType()==LineChange.ADD){
				String content = lineChange.getLineContent();
				content = content.substring(1, content.length());
				
				ASTNode node = parseAST(content);
				MethodInvocationFinder finder = new MethodInvocationFinder();
				node.accept(finder);
				
				if(finder.isFound){
					int line = chunk.getLineNumberInTarget(lineChange);
					addedInvocations.put(line, finder.methodName);
				}
			}
		}

		if(!addedInvocations.isEmpty()){
			for(Integer addedLine: addedInvocations.keySet()){
				if(removedInvocations.isEmpty()){
					return true;
				}
				
				for(Integer removedLine: removedInvocations.keySet()){
					List<Integer> targetLines = filePair.getSourceToTargetMap().get(removedLine);
					if(targetLines!=null && targetLines.contains(addedLine)){
						String methodBefore = removedInvocations.get(removedLine);
						String methodAfter = addedInvocations.get(addedLine);
						if(!methodBefore.equals(methodAfter)){
							return true;
						}
					}
				}
			}
		}
		
		return false;
	}

	@Override
	public SolutionPattern getSolutionPattern() {
		return new SolutionPattern(SolutionPattern.INVOKE_NEW_METHOD);
	}

}
