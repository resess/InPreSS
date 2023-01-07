package resess;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

import org.apache.poi.ss.usermodel.Row;
import ca.ubc.ece.resess.slicer.dynamic.slicer4j.Slicer;
import microbat.codeanalysis.bytecode.ByteCodeParser;
import microbat.codeanalysis.bytecode.MethodFinderByLine;
import microbat.model.BreakPoint;
import microbat.model.ClassLocation;
import microbat.model.trace.Trace;
import microbat.model.trace.TraceNode;
import microbat.model.trace.TraceNodeOrderComparator;
import microbat.model.value.VarValue;
import sav.common.core.Pair;
import soot.ValueBox;
import tregression.StepChangeType;
import tregression.StepChangeTypeChecker;
import tregression.empiricalstudy.TestCase;
import tregression.model.PairList;
import tregression.model.TraceNodePair;
import tregression.separatesnapshots.DiffMatcher;

public class dualSlicingWithErease {
	private boolean isMatchable(TraceNode invocationParent, PairList pairList, boolean isOnBefore) {
		if(isOnBefore){
			TraceNodePair pair = pairList.findByBeforeNode(invocationParent);
			if(pair!=null){
				if(pair.getAfterNode()!=null){
					return true;
				}
			}
		}
		else{
			TraceNodePair pair = pairList.findByAfterNode(invocationParent);
			if(pair!=null){
				if(pair.getBeforeNode()!=null){
					return true;
				}
			}
		}
		return false;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////	
	private TraceNode findLatestControlDifferent(TraceNode currentNode, TraceNode controlDom, 
			StepChangeTypeChecker checker, PairList pairList, DiffMatcher matcher) {
		TraceNode n = currentNode.getStepInPrevious();
		StepChangeType t = checker.getType(n, true, pairList, matcher);
		while(t.getType()==StepChangeType.CTL && n.getOrder()>controlDom.getOrder()){
			TraceNode dom = n.getInvocationMethodOrDominator();
			if(dom.getMethodSign().equals(n.getMethodSign())){
				return n;
			}
			
			n = n.getStepInPrevious();
			t = checker.getType(n, true, pairList, matcher);
		}
		return controlDom;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void printDualSliceResults(List<TraceNode> visited, boolean isNew, String proPath, DiffMatcher matcher) {
		PrintWriter writer;
		try {
		String onNew = isNew ? "new" : "old";
		writer = new PrintWriter(proPath + "/results/" + onNew + "/DualSlice.txt", "UTF-8");
		for (int i = visited.size() - 1; i >= 0; i--) {
		   writer.println(getSourceCode(visited.get(i),isNew,matcher));
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
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	public int findStartOrderInOtherTrace(TraceNode problematicStep, PairList pairList, boolean isOnBeforeTrace) {
		TraceNode node = problematicStep.getStepInPrevious();
		while(node != null) {
			TraceNode matchedNode = null;
			if(isOnBeforeTrace) {
				TraceNodePair pair = pairList.findByBeforeNode(node);
				if(pair != null) {
					matchedNode = pair.getAfterNode();
				}
			}
			else {
				TraceNodePair pair = pairList.findByAfterNode(node);
				if(pair != null) {
					matchedNode = pair.getBeforeNode();
				}
			}
			
			
			if(matchedNode != null) {
				return matchedNode.getOrder();
			}
			
			node = node.getStepInPrevious();
			
		}
		
		return 1;
	}
	public int findEndOrderInOtherTrace(TraceNode problematicStep, PairList pairList, boolean isOnBeforeTrace, Trace otherTrace) {
		TraceNode node = problematicStep.getStepInNext();
		while(node != null) {
			TraceNode matchedNode = null;
			if(isOnBeforeTrace) {
				TraceNodePair pair = pairList.findByBeforeNode(node);
				if(pair != null) {
					matchedNode = pair.getAfterNode();
				}
			}
			else {
				TraceNodePair pair = pairList.findByAfterNode(node);
				if(pair != null) {
					matchedNode = pair.getBeforeNode();
				}
			}
			
			
			if(matchedNode != null) {
				return matchedNode.getOrder();
			}
			
			node = node.getStepInNext();
		}
		
		/**
		 * Then, all the steps after problemStep cannot be matched in the other trace. 
		 */
		int order0 = findStartOrderInOtherTrace(problematicStep, pairList, isOnBeforeTrace);
		if(order0+1<=otherTrace.size()){
			TraceNode n = otherTrace.getExecutionList().get(order0);
			while(n!=null){
				if(n.isConditional()){
					if(n.getStepOverNext()!=null){
						return n.getStepOverNext().getOrder();
					}
					else{
						return n.getOrder();						
					}
				}
				else{
					if(n.getStepOverNext()!=null){
						n=n.getStepOverNext();						
					}
					else{
						n=n.getStepInNext();
					}
				}
			}
		}
		return otherTrace.size();
		
		/**
		 * The the length of the other trace.
		 */
//		TraceNode n = null;
//		int size = pairList.getPairList().size();
//		if(isOnBeforeTrace) {
//			n = pairList.getPairList().get(size-1).getAfterNode();
//		}
//		else {
//			n = pairList.getPairList().get(size-1).getBeforeNode();
//		}
//		int order = n.getOrder();
//		while(n!=null) {
//			n = n.getStepInNext();
//			if(n!=null) {
//				order = n.getOrder();
//			}
//		}
//		return order;
	}
	public TraceNode findControlMendingNodeOnOtherTrace(TraceNode problematicStep, PairList pairList,
			Trace otherTrace, boolean isOtherTraceTheBeforeTrace, ClassLocation correspondingLocation, DiffMatcher matcher) {
		
		int startOrder = findStartOrderInOtherTrace(problematicStep, pairList, !isOtherTraceTheBeforeTrace);
		int endOrder = findEndOrderInOtherTrace(problematicStep, pairList, !isOtherTraceTheBeforeTrace, otherTrace);
		System.currentTimeMillis();
		TraceNode bestNode = null;
		int value = -1;
		
		//TODO this implementation is problematic, I need to use soot to analyze the static control dependence relation.
		TraceNode temp = null;
		for(int i=endOrder; i>=startOrder; i--){
			if(i<=otherTrace.size()) {
				TraceNode node = otherTrace.getExecutionList().get(i-1);
				if(node.isConditional()){
					temp = node;
					if(node.getControlScope().containLocation(correspondingLocation)) {
						if(bestNode==null) {
							TraceNode programaticInvocationParent = problematicStep.getInvocationParent();
							TraceNode invocationParent = node.getInvocationParent();
							
							if(programaticInvocationParent==null && invocationParent==null) {
								bestNode = node;								
							}
							else if(programaticInvocationParent!=null && invocationParent!=null){
								if(pairList.isPair(programaticInvocationParent, 
										invocationParent, !isOtherTraceTheBeforeTrace)) {
									bestNode = node;
								}
							}
						}
					}
					else{
						List<TraceNode> allControlDominatees = node.findAllControlDominatees();
						for(TraceNode controlDominatee: allControlDominatees){
							if(controlDominatee.isException()){
								if(value==-1) {
									bestNode = node;
									value++;
								}
								else {
									List<TraceNode> allDominatees = bestNode.findAllControlDominatees();
									if(allDominatees.contains(node)) {
										bestNode = node;
									}
								}
							}
						}
					}
					
				}			
				else{
					BreakPoint correspondingPoint = new BreakPoint(correspondingLocation.getClassCanonicalName(), null, correspondingLocation.getLineNumber());
					MethodFinderByLine finder = new MethodFinderByLine(node.getBreakPoint());
					
					
					ByteCodeParser.parse(node.getClassCanonicalName(), finder, node.getTrace().getAppJavaClassPath());
					
					if(finder.getMethod()!=null){
						String methodSign = correspondingLocation.getClassCanonicalName() + "#" + finder.getMethod().getName() + finder.getMethod().getSignature();
						if(node.getMethodSign().equals(methodSign)){
							if(node.getLineNumber()<correspondingPoint.getLineNumber()){
								if(finder.isThrow() || finder.isReturn()){
									bestNode = node;
								}
							}
						}
					}
					
				}
			}
		}
		
		if(bestNode==null){
			bestNode = temp;
		}
		
		return bestNode;
	}
	public void dualSlicing(String basePath, String projectName, String bugID, TestCase tc,
			boolean slicer4J, String proPath, TraceNode observedFaultNode, Trace newTrace, Trace oldTrace, PairList dualPairList, PairList inPreSSPairList, 
			DiffMatcher matcher, int oldTraceTime, int newTraceTime, int codeTime, int traceTime ) throws IOException {

		List<TraceNode> new_workList = new ArrayList<>();
		List<TraceNode> new_visited = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> new_ctl_map = new HashMap<>();

		List<TraceNode> old_workList = new ArrayList<>();
		List<TraceNode> old_visited = new ArrayList<>();
		HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map = new HashMap<>();
		HashMap<TraceNode, List<TraceNode>> old_ctl_map = new HashMap<>();
		

		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> old_CashDeps = new HashMap<>();
		HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> new_CashDeps = new HashMap<>();
		
		
		new_visited.add(observedFaultNode);
		new_workList.add(observedFaultNode);
		System.out.println("#############################");
		System.out.println("Starting Working list");
		
		

		StepChangeTypeChecker typeChecker = new StepChangeTypeChecker(newTrace, oldTrace);

		Long dual_start_time = System.currentTimeMillis();
		while(!new_workList.isEmpty() || !old_workList.isEmpty()){
			while(!new_workList.isEmpty()) {
				System.out.println("#############################");
				TraceNode step = new_workList.remove(0);
			    updateWorklist(new_CashDeps, old_CashDeps, step, newTrace, oldTrace, new_visited, new_workList,old_visited,old_workList,true,typeChecker,
			    		dualPairList,matcher,new_data_map,new_ctl_map, proPath);				
			}
			////////////////////////////////////////////////////////////////////////////////////////
			while(!old_workList.isEmpty()) {
				System.out.println("#############################");
				TraceNode step = old_workList.remove(0);
				updateWorklist(old_CashDeps, new_CashDeps, step, oldTrace, newTrace, old_visited,old_workList,new_visited, new_workList,false,typeChecker,
						dualPairList,matcher,old_data_map,old_ctl_map, proPath);
			}			
		}
		/// ################################################################
		/// ################################################################
		Long dual_finish_time = System.currentTimeMillis();				
		int dual_Time = (int) (dual_finish_time - dual_start_time);
		
		for(int i=old_visited.size()-1;i>=0; i--){
			TraceNode step = old_visited.get(i);
			if(step==null)
				old_visited.remove(i);
		}
		for(int i=new_visited.size()-1;i>=0; i--){
			TraceNode step = new_visited.get(i);
			if(step==null)
				new_visited.remove(i);
		}	
		System.out.println("##########Finish Dual Slciing###################");
		printDualSliceResults(old_visited, false, proPath, matcher);
		printDualSliceResults(new_visited,true, proPath,matcher);
		/// ################################################################
		/// ################################################################
		HashMap<Integer, Integer> oldChangeChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newChangeChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> oldTestCaseChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newTestCaseChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> oldCommonChunkInfo = new HashMap<>();
		HashMap<Integer, Integer> newCommonChunkInfo = new HashMap<>();
		getChangeChunks(typeChecker, matcher, old_visited,new_visited,oldChangeChunkInfo,newChangeChunkInfo);
//		getChangeChunks(typeChecker, inPreSSPairList, matcher, old_visited,new_visited,oldChangeChunkInfo,newChangeChunkInfo);
		getTestCaseChunks(tc,old_visited,new_visited,oldTestCaseChunkInfo,newTestCaseChunkInfo);
		getCommonBlocksChunks(typeChecker, matcher, tc,old_visited,new_visited,oldCommonChunkInfo,newCommonChunkInfo);
//		getCommonBlocksChunks(typeChecker, inPreSSPairList, matcher, tc,old_visited,new_visited,oldCommonChunkInfo,newCommonChunkInfo);
		System.out.println("##############Printing Abstraction to Graph##############");
		HashMap<TraceNode, List<Pair<TraceNode, String>>> both_new_data_map = new_data_map;
		HashMap<TraceNode, List<TraceNode>> both_new_ctl_map = new_ctl_map;
		HashMap<TraceNode, List<Pair<TraceNode, String>>> both_old_data_map = old_data_map;
		HashMap<TraceNode, List<TraceNode>> both_old_ctl_map = old_ctl_map;
		///################################################################
		///################################################################
		System.out.println("##############Final Results with circles (same function index) + common triangles ##############");	
		List<TraceNode> old_kept = new ArrayList<>();
		List<TraceNode> new_kept = new ArrayList<>();		
		List<TraceNode> old_retained = new ArrayList<>();		
		List<TraceNode> new_retained = new ArrayList<>();

		addingClientTestNodes(tc, oldTrace.getExecutionList(), newTrace.getExecutionList(), old_kept, new_kept, old_retained, new_retained);		
		//addingClientTestNodes(tc, old_visited, new_visited, old_kept, new_kept, old_retained, new_retained);
		int oldRetainedTestRemovedByDual = getRetainedTestRemovedByDual(tc, oldTrace.getExecutionList(),old_visited);
		int newRetainedTestRemovedByDual = getRetainedTestRemovedByDual(tc, newTrace.getExecutionList(),new_visited);
		
		
		HashMap<Integer, List<TraceNode>> oldDataBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newDataBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> oldCtlBlockNodes = new HashMap<>();
		HashMap<Integer, List<TraceNode>> newCtlBlockNodes = new HashMap<>();
		long inPreSS_start_time = System.currentTimeMillis();	
		inPreSSAbstractionCircleOnlySameFunctionsCommonTrianlges(tc, proPath, old_visited,new_visited,typeChecker,dualPairList,inPreSSPairList, 
				matcher,both_old_data_map,both_old_ctl_map,both_new_data_map,both_new_ctl_map,old_kept, new_kept, 
				oldDataBlockNodes, newDataBlockNodes, oldCtlBlockNodes, newCtlBlockNodes, old_retained, new_retained);
		long inPreSS_finish_time = System.currentTimeMillis();			
		int inPreSS_Time = (int) (inPreSS_finish_time - inPreSS_start_time);
		PrintFinalResultAll(tc,basePath, projectName, bugID, newTrace, oldTrace, new_visited, old_visited, new_kept, old_kept, new_retained, 
				old_retained, newDataBlockNodes, oldDataBlockNodes, newCtlBlockNodes, oldCtlBlockNodes, oldTraceTime, newTraceTime, codeTime, 
				traceTime, dual_Time, inPreSS_Time,oldChangeChunkInfo,newChangeChunkInfo,oldTestCaseChunkInfo,newTestCaseChunkInfo, oldCommonChunkInfo, newCommonChunkInfo,oldRetainedTestRemovedByDual,newRetainedTestRemovedByDual);			
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private int getRetainedTestRemovedByDual(TestCase tc, List<TraceNode> executionList, List<TraceNode> visited) {
		int res = 0;
		for (TraceNode node: executionList) {
			String ClassName = node.getClassCanonicalName();
			if (tc.testClass.equals(ClassName)) {			
				if(visited.contains(node)) {
				   //it is already kept by us.
			    }
				else {
				  res++;
			}			
		   }
		}
		return res;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void getCommonBlocksChunks(StepChangeTypeChecker typeChecker, DiffMatcher matcher, TestCase tc, List<TraceNode> old_visited, List<TraceNode> new_visited,
				HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo) {
		int CurrentChunk=0;
		boolean PreviousStatementWasCommon = false;
		int NomberInJustFinishedChunk=0;
		for (int i = 0; i <= old_visited.size()-1; i++) {
			TraceNode step = old_visited.get(i);	
			boolean isSourceDiff = matcher.checkSourceDiff(step.getBreakPoint(), false);		
			if(isATestStatement(tc,step) || isSourceDiff) {		
				if(PreviousStatementWasCommon) {//finish the current block	
					if(NomberInJustFinishedChunk!=0)
					    oldCommonChunkInfo.put(CurrentChunk,NomberInJustFinishedChunk);
				}
				else {
					//nothing: the previous one was also retain
				}
				PreviousStatementWasCommon = false;
				
			}else { 
				if(PreviousStatementWasCommon) {
				   NomberInJustFinishedChunk++;//add to currentBlock
				}else {//start a new chunk
					CurrentChunk++;		
					NomberInJustFinishedChunk=1;
				}	    
		    PreviousStatementWasCommon=true;
			}		
		}
		 CurrentChunk=0;
		 PreviousStatementWasCommon = false;
		 NomberInJustFinishedChunk=0;
		for (int i = 0; i <= new_visited.size()-1; i++) {
			TraceNode step = new_visited.get(i);	
			boolean isSourceDiff = matcher.checkSourceDiff(step.getBreakPoint(), true);		
			if(isATestStatement(tc,step) || isSourceDiff) {		
				if(PreviousStatementWasCommon) {//finish the current block	
					if(NomberInJustFinishedChunk!=0)
					    newCommonChunkInfo.put(CurrentChunk,NomberInJustFinishedChunk);
				}
				else {
					//nothing: the previous one was also retain
				}
				PreviousStatementWasCommon = false;
				
			}else { 
				if(PreviousStatementWasCommon) {
				   NomberInJustFinishedChunk++;//add to currentBlock
				}else {//start a new chunk
					CurrentChunk++;		
					NomberInJustFinishedChunk=1;
				}	    
		    PreviousStatementWasCommon=true;
			}		
		}
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void addingClientTestNodes(TestCase tc, List<TraceNode> old_visited, List<TraceNode> new_visited, List<TraceNode> old_kept,
				List<TraceNode> new_kept, List<TraceNode> old_retained, List<TraceNode> new_retained) {
		for (TraceNode node: old_visited) {
			String ClassName = node.getClassCanonicalName();
			if (tc.testClass.equals(ClassName)) {
					if(!old_kept.contains(node)) {
						old_kept.add(node);
						old_retained.add(node);
					}			
			}
		}
		for (TraceNode node: new_visited) {
			String ClassName = node.getClassCanonicalName();
			if (tc.testClass.equals(ClassName)) {
					if(!new_kept.contains(node)) {
						new_kept.add(node);
						new_retained.add(node);
					}
				
			}
		}
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void getTestCaseChunks(TestCase tc, List<TraceNode> old_visited, List<TraceNode> new_visited,
			HashMap<Integer, Integer> oldTestChunkInfo, HashMap<Integer, Integer> newTestChunkInfo) {
	//Collections.sort(old_visited, new TraceNodePairOrderComparator());
	//Collections.sort(new_visited, new TraceNodePairOrderComparator());
	int CurrentChunk=0;
	boolean PreviousStatementWasTest = false;
	for (int i = 0; i <= old_visited.size()-1; i++) {
		TraceNode step = old_visited.get(i);	
		if(isATestStatement(tc,step)) {
			if(PreviousStatementWasTest) {
				//do nothing. We can add all changed statements to the arry for the chunck
			}
			else {
				CurrentChunk++;
				oldTestChunkInfo.put(CurrentChunk, step.getOrder());//this the first statement of this chunk just add it
			}
			PreviousStatementWasTest = true;
			
		}else {
			PreviousStatementWasTest=false;
		}
		
	}
	CurrentChunk = 0;
	PreviousStatementWasTest = false;
	for (int i = 0; i <= new_visited.size()-1; i++) {
		TraceNode step = new_visited.get(i);	
		if(isATestStatement(tc,step)) {
			if(PreviousStatementWasTest) {
				//do nothing. We can add all changed statements to the arry for the chunck
			}
			else {
				CurrentChunk++;
				newTestChunkInfo.put(CurrentChunk, step.getOrder());//this the first statement of this chunk just add it
			}
			PreviousStatementWasTest = true;
			
		}else {
			PreviousStatementWasTest=false;
		}
		
	  }
		
	}
	private void getChangeChunks(StepChangeTypeChecker typeChecker, DiffMatcher matcher, List<TraceNode> old_visited, List<TraceNode> new_visited,
				HashMap<Integer, Integer> oldChangeChunkInfo, HashMap<Integer, Integer> newChangeChunkInfo) {
		Collections.sort(old_visited, new TraceNodeOrderComparator());
		Collections.sort(new_visited, new TraceNodeOrderComparator());
		int CurrentChunk=0;
		boolean PreviousStatementWasChange = false;
		for (int i = 0; i <= old_visited.size()-1; i++) {
			TraceNode step = old_visited.get(i);
			boolean isSourceDiff = matcher.checkSourceDiff(step.getBreakPoint(), false);		
			if(isSourceDiff) {
				if(PreviousStatementWasChange) {
					//do nothing. We can add all changed statements to the arry for the chunck
				}
				else {
					CurrentChunk++;
					oldChangeChunkInfo.put(CurrentChunk, step.getOrder());//this the first statement of this chunk just add it
				}
				PreviousStatementWasChange = true;
				
			}else {
				PreviousStatementWasChange=false;
			}
			
		}
		CurrentChunk=0;
		PreviousStatementWasChange = false;
		for (int i = 0; i <= new_visited.size()-1; i++) {
			TraceNode step = new_visited.get(i);
			boolean isSourceDiff = matcher.checkSourceDiff(step.getBreakPoint(), true);		
			if(isSourceDiff) {
				if(PreviousStatementWasChange) {
					//do nothing. We can add all changed statements to the arry for the chunck
				}
				else {
					CurrentChunk++;
					newChangeChunkInfo.put(CurrentChunk, step.getOrder());
				}
				PreviousStatementWasChange = true;
				
			}else {
				PreviousStatementWasChange=false;
			}
			
		}
			
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void updateWorklist( HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> cashDeps, HashMap<TraceNode, 
			HashMap<Pair<TraceNode, String>, String>> OthercashDeps, TraceNode step, Trace trace, Trace otherTrace, List<TraceNode> visited, 
			List<TraceNode> workList, List<TraceNode> other_visited, List<TraceNode> other_workList, boolean isNew, 
			StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher, HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map, 
			HashMap<TraceNode, List<TraceNode>> ctl_map, String proPath) {
		if(step==null)
			return;
		StepChangeType changeType = typeChecker.getType(step, isNew, pairList, matcher);	
		String onNew = isNew?"new":"old";
		System.out.println("On " + onNew + " trace," + step);
		////////////////////////////////////////////////////////////////////
		if(changeType.getType()==StepChangeType.SRC){
			System.out.println("debug: node is src diff");
			TraceNode matchedStep = changeType.getMatchingStep();	
			if(matchedStep!=null) {
				if(!other_visited.contains(matchedStep)) { 
					other_visited.add(matchedStep);
					other_workList.add(matchedStep);					
				}
			}		
		}
		////////////////////////////////////////////////////////////////////
		//////////////////add corresponding node if it is data//////////////////
		if(changeType.getType()==StepChangeType.DAT){
			System.out.println("debug: node is data diff");
			TraceNode matchedStep = changeType.getMatchingStep();
			if(!other_visited.contains(matchedStep)) { 
				other_visited.add(matchedStep);
				other_workList.add(matchedStep);					
			}
		}
		////////////////////////////////////////////////////////////////////
		//////////////////add control mending//////////////////
		if(changeType.getType()==StepChangeType.CTL){
			System.out.println("debug: node is control diff");
			ClassLocation correspondingLocation = matcher.findCorrespondingLocation(step.getBreakPoint(), !isNew);	
			//System.out.println("debug: corresponding location:" + correspondingLocation.toString());
			TraceNode otherControlDom = findControlMendingNodeOnOtherTrace(step, pairList, otherTrace, !isNew, correspondingLocation, matcher);
			//System.out.println("debug: otherControlDom location:" + otherControlDom.toString());
			if(!other_visited.contains(otherControlDom)) { 
				other_visited.add(otherControlDom);
				other_workList.add(otherControlDom);
			}			
		}
		////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////
		
		HashMap<Pair<TraceNode, String>, String> deps = new HashMap<>();//map the <dep node, the var> and data/control		
		deps = getDirectDependencies(cashDeps, changeType, step, trace, isNew, typeChecker, pairList, matcher);
		
		////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////
		for(Pair<TraceNode, String> d: deps.keySet()){
			//System.out.println("dep node is " + d.first());						
			StepChangeType chgType = typeChecker.getType(d.first(), isNew, pairList, matcher);	
			if(chgType.getType()!=StepChangeType.IDT) {
				//System.out.println("not identical ");
				if(deps.get(d)=="data") {
					List<Pair<TraceNode, String>> dataDeps = data_map.get(step);
					if(dataDeps==null) {
						dataDeps = new ArrayList<>();
					}
					dataDeps.add(d);					
					data_map.put(step, dataDeps);
				}
				else if(deps.get(d)=="control") {
					List<TraceNode> ctlDeps = ctl_map.get(step);
					if(ctlDeps==null) {
						ctlDeps = new ArrayList<>();
					}
					ctlDeps.add(d.first());
					ctl_map.put(step, ctlDeps);
				}

				if(!visited.contains(d.first())) {
					workList.add(d.first());
					visited.add(d.first());						
				}
			}
			else {//if it is IDT
				//System.out.println("dep is identical ");
				if(changeType.getType()==StepChangeType.DAT){				
					TraceNode corresponding = changeType.getMatchingStep();//corresponding node of step in the other trace 
					//System.out.println("corresponding node:" + corresponding);
					if(corresponding!=null) {
						HashMap<Pair<TraceNode, String>, String> corresponding_deps = new HashMap<>();//the deps of corresponding nodes
						
						corresponding_deps = getDirectDependencies(OthercashDeps, changeType, corresponding, otherTrace, !isNew, typeChecker, pairList, matcher);
												
						boolean found = false;
						for(Pair<TraceNode, String> dd: corresponding_deps.keySet()){
							StepChangeType tepmType = typeChecker.getType(dd.first(), !isNew, pairList, matcher);		
							TraceNode correspondingDeps = tepmType.getMatchingStep();
							if(d.first().equals(correspondingDeps))//already in the slice
								found = true;
						}
						if(!found){
							//System.out.println("different def-use");
							if(deps.get(d)=="data") {
								List<Pair<TraceNode, String>> dataDeps = data_map.get(step);
								if(dataDeps==null) {
									dataDeps = new ArrayList<>();
								}
								dataDeps.add(d);
								data_map.put(step, dataDeps);
							}
							else if(deps.get(d)=="control") {
								List<TraceNode> ctlDeps = ctl_map.get(step);
								if(ctlDeps==null) {
									ctlDeps = new ArrayList<>();
								}
								ctlDeps.add(d.first());
								ctl_map.put(step, ctlDeps);
							}
							
							if(!visited.contains(d.first())) { 								
									visited.add(d.first());	//just add to visited not the worklist							
							}
						}						
					}
				}
				if(d.first().isException()){
					TraceNode nextStep = d.first().getStepInPrevious();
					//System.out.println("debug: prev step " + nextStep);
					List<TraceNode> ctlDeps = ctl_map.get(step);
					if(ctlDeps==null) {
						ctlDeps = new ArrayList<>();
					}
					ctlDeps.add(nextStep);
					ctl_map.put(step, ctlDeps);
					if(!visited.contains(nextStep)) {
						workList.add(nextStep);
						visited.add(nextStep);							
					}						
				}
			}	
		}
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////	
	private HashMap<Pair<TraceNode, String>, String> getDirectDependencies(HashMap<TraceNode, HashMap<Pair<TraceNode, String>, String>> cashDeps, 
			StepChangeType changeType, TraceNode step, Trace trace, boolean isNew, StepChangeTypeChecker typeChecker, PairList pairList, DiffMatcher matcher) {
		if(cashDeps.containsKey(step))
			return cashDeps.get(step);
		HashMap<Pair<TraceNode, String>, String> deps = new HashMap<>();
		//////////////////add dependency nodes//////////////////
		//add all def-use
		for(VarValue readVar: step.getReadVariables()){
			TraceNode dataDom = trace.findDataDependency(step, readVar);
			//System.out.println("debug: data dependency node: " + dataDom);
			if(dataDom!=null) {
				Pair<TraceNode, String> keyPair = new Pair(dataDom, "null");
				deps.put(keyPair,"data");
			}
		}
		
		//////////////////add control node//////////////////
		TraceNode controlDom = step.getInvocationMethodOrDominator();
		//System.out.println("debug: control dep node (dominator): " + controlDom);	
		if(step.insideException() || getSourceCode(step, isNew, matcher).contains("throw")){
			controlDom = step.getStepInPrevious();
			//System.out.println("debug: control dep node (exception): " + controlDom);
		}
		else if(controlDom!=null && !controlDom.isConditional() && controlDom.isBranch() && !controlDom.equals(step.getInvocationParent())){					
			StepChangeType t = typeChecker.getType(controlDom, isNew, pairList, matcher);
			if(t.getType()==StepChangeType.IDT){
				controlDom = findLatestControlDifferent(step, controlDom, typeChecker, pairList, matcher);						
			}
		}						
		if(controlDom==null){
			TraceNode invocationParent = step.getInvocationParent();
			//System.out.println("debug: control dep node (invocation): " + invocationParent);
			if(!isMatchable(invocationParent, pairList, isNew)){
				controlDom = invocationParent;
				//System.out.println("debug: control dep node (not matchable): " + controlDom);
			}
		}   
		//System.out.println("debug: control dependency node: " + controlDom);
		if(controlDom!=null) {
			Pair<TraceNode, String> keyPair = new Pair(controlDom, "null");
			deps.put(keyPair, "control");
		}
		cashDeps.put(step, deps);
		return deps;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////	
	public String getSourceCode(TraceNode traceNode, boolean isOnNew, DiffMatcher matcher) {
		
		int lineNo = traceNode.getLineNumber();	
		String source = null;
        BreakPoint breakPoint = traceNode.getBreakPoint();
        String Path = breakPoint.getFullJavaFilePath();
		File file = new File(Path);
//		if(!file.exists()){
//			path = path.replace(matcher.getSourceFolderName(), matcher.getTestFolderName());
//			file = new File(path);
//		}
		
		if(file.exists()){
			InputStream stdin;
			try {
				stdin = new FileInputStream(file);
				InputStreamReader isr = new InputStreamReader(stdin);
				BufferedReader br = new BufferedReader(isr);

				String line = null;
				int index = 1;
				while ( (line = br.readLine()) != null){					
					if(index==lineNo) {
						source = line.trim();
						source= source.replace("\"", "'");
					}
					index++;
				}				
			} catch (FileNotFoundException e1) {
				e1.printStackTrace();
			} catch (IOException e1) {
				e1.printStackTrace();
			}
		}
		
		String result = String.valueOf(traceNode.getOrder());
		result = traceNode.getClassCanonicalName();
		String methodName = traceNode.getMethodName();
		if(methodName != null){
			result = result + ":" + methodName;
		}
		result = result + ": LineNo@" + traceNode.getLineNumber() + "--->";
        result = result + source;
		return result;
		
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void inPreSSAbstractionCircleOnlySameFunctionsCommonTrianlges(TestCase tc,String proPath, List<TraceNode> old_visited, List<TraceNode> new_visited, 
			StepChangeTypeChecker typeChecker, PairList dualPairList, PairList inPreSSPairList, DiffMatcher matcher, 
			HashMap<TraceNode, List<Pair<TraceNode, String>>> old_data_map, HashMap<TraceNode, List<TraceNode>> old_ctl_map, 
			HashMap<TraceNode, List<Pair<TraceNode, String>>> new_data_map, HashMap<TraceNode, List<TraceNode>> new_ctl_map, 
			List<TraceNode> old_kept, List<TraceNode> new_kept, HashMap<Integer, List<TraceNode>> oldDataBlockNodes, 
			HashMap<Integer, List<TraceNode>> newDataBlockNodes,HashMap<Integer, List<TraceNode>> oldCtlBlockNodes,
			HashMap<Integer, List<TraceNode>> newCtlBlockNodes, List<TraceNode> old_retained, List<TraceNode> new_retained) {
		/////////////////////////////////////////////////////////////
		PairList pairList = dualPairList;
//		PairList pairList = inPreSSPairList;
		Collections.sort(old_visited, new TraceNodeOrderComparator());
		Collections.sort(new_visited, new TraceNodeOrderComparator());                	
		/////////////////////extract blocks for old/////////////////////
		HashMap<TraceNode, Integer> oldBlocks = new HashMap<>();
		Integer BlockID = 0;
		boolean current_data_flag = false;
		boolean current_ctl_flag = false;
		boolean firstTime = true;
		boolean isDataBlock = false;
		boolean isCTLBlock = false;
		for(int i=old_visited.size()-1;i>=0; i--){
			TraceNode step = old_visited.get(i);	
			//System.out.println("step on old is: " + step);	
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
			//if ((changeType.getType()!=StepChangeType.DAT || i==old_visited.size()-1) && changeType.getType()!=StepChangeType.CTL) { //separate the blocks
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL) || isATestStatement(tc, step) ) { //it is retain		
				isDataBlock = false;
				isCTLBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isCTLBlock = true;
				if (!current_ctl_flag) {//if we are not currently in ctl block
					BlockID = BlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;				
				if (!current_data_flag) {//if we are not currently in data block
					BlockID = BlockID + 1;
					current_data_flag = true;
					current_ctl_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
	//		if(firstTime) {
	//			firstTime = false;
	//			BlockID = BlockID + 1;
	//		}
			
	//		oldBlocks.put(step, BlockID);	
			
		}	
		System.out.println("old blocks " + oldBlocks);	
		/////////////////////extract blocks for new/////////////////////
		HashMap<TraceNode, Integer> newBlocks = new HashMap<>();
		BlockID = 0;
		current_data_flag = false;
		current_ctl_flag = false;
		firstTime = true;
		isDataBlock = false;
		TraceNode previousData = null;
		for(int i=new_visited.size()-1;i>=0; i--){
			TraceNode step = new_visited.get(i);
			//System.out.println("step on new is: " + step);	
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
			//if ((changeType.getType()!=StepChangeType.DAT || i==new_visited.size()-1) && changeType.getType()!=StepChangeType.CTL) { //separate the blocks
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL) || isATestStatement(tc, step) ) { //separate the blocks				
				isDataBlock = false;
				isCTLBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isCTLBlock = true;
				if (!current_ctl_flag) {//coming from dat or other blocks
					BlockID = BlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					//firstTime = false;
				}
				newBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;	
				if (previousData!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, true, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();
					if(oldBlocks.get(matchedStep)!=oldBlocks.get(previousMatchedStep)) {//separate if it is separated in old 									
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						//firstTime = false;
					}					
					else {			
						if (!current_data_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = true;
							current_ctl_flag = false;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_data_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						//firstTime = false;
					}
					
				}
				previousData = step;
				newBlocks.put(step, BlockID);	
			}
	//		if (firstTime) {
	//			BlockID = BlockID + 1;
	//			firstTime = false;
	//		}
	//		newBlocks.put(step, BlockID);
		
			if (isDataBlock){
				if (newDataBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = newDataBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newDataBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newDataBlockNodes.put(BlockID, nodes);
				}
			}
			if (isCTLBlock){
				if (newCtlBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = newCtlBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					newCtlBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					newCtlBlockNodes.put(BlockID, nodes);
				}
			}	
		}
		System.out.println("new blocks " + newBlocks);
		/////////////////////extract blocks for old/////////////////////
		oldBlocks = new HashMap<>();
		BlockID = 0;
		current_data_flag = false;
		current_ctl_flag = false;
		firstTime = true;
		isDataBlock = false;
		previousData = null;
		for(int i=old_visited.size()-1;i>=0; i--){
			TraceNode step = old_visited.get(i);
			StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
			if ((changeType.getType()!=StepChangeType.DAT && changeType.getType()!=StepChangeType.CTL) || isATestStatement(tc, step) ) { //separate the blocks
				isDataBlock = false;
				isCTLBlock = false;
				if (current_data_flag) {//coming from a data block
					//BlockID = BlockID + 1;
					current_data_flag = false;
					//firstTime = false;
				}
				if (current_ctl_flag) {//coming from a ctl block
					//BlockID = BlockID + 1;
					current_ctl_flag = false;
					//firstTime = false;
				}
			}
			else if (changeType.getType()==StepChangeType.CTL){ 
				isDataBlock = false;
				isCTLBlock = true;
				if (!current_ctl_flag) {//coming from dat or other blocks
					BlockID = BlockID + 1;
					current_ctl_flag = true;
					current_data_flag = false;
					//firstTime = false;
				}
				oldBlocks.put(step, BlockID);
			}
			else if (changeType.getType()==StepChangeType.DAT){ 
				isDataBlock = true;
				isCTLBlock = false;	
				if (previousData!=null) {
					StepChangeType previousChangeType = typeChecker.getType(previousData, false, pairList, matcher);
					TraceNode matchedStep = changeType.getMatchingStep();
					TraceNode previousMatchedStep =	previousChangeType.getMatchingStep();
					if(newBlocks.get(matchedStep)!=newBlocks.get(previousMatchedStep)) {//separate them 									
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						//firstTime = false;
					}					
					else {			
						if (!current_data_flag) {//coming from ctl or other blocks
							BlockID = BlockID + 1;
							current_data_flag = true;
							current_ctl_flag = false;
							//firstTime = false;
						}
					}
				}
				else {		
					if (!current_data_flag) {//coming from ctl or other blocks
						BlockID = BlockID + 1;
						current_data_flag = true;
						current_ctl_flag = false;
						//firstTime = false;
					}
				}
				previousData = step;
				oldBlocks.put(step, BlockID);
			}
	//		if (firstTime) {
	//			BlockID = BlockID + 1;
	//			firstTime = false;
	//		}
	//		oldBlocks.put(step, BlockID);
			if (isDataBlock){
				if (oldDataBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = oldDataBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldDataBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldDataBlockNodes.put(BlockID, nodes);
				}
			}
			if (isCTLBlock){
				if (oldCtlBlockNodes.containsKey(BlockID)){
					List<TraceNode> nodes = oldCtlBlockNodes.get(BlockID);
					if (nodes==null)
						nodes = new ArrayList<>();
					nodes.add(step);
					oldCtlBlockNodes.put(BlockID, nodes);
				}
				else {
					List<TraceNode> nodes = new ArrayList<>();
					nodes.add(step);
					oldCtlBlockNodes.put(BlockID, nodes);
				}
			}
		}
		System.out.println("#################after paralizing#################"); 
		System.out.println("The # of data block in old " + oldDataBlockNodes.keySet().size());
		System.out.println("The # of data block in new " + newDataBlockNodes.keySet().size());
		System.out.println("The # of ctl block in old " + oldCtlBlockNodes.keySet().size());
		System.out.println("The # of ctl block in new " + newCtlBlockNodes.keySet().size());
	
		////////////////////////////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////////////////////////////
		////////////////////////////////////////////////////////////////////////////////////////////////////////	
		////////////////////////////////////////////////////////////////////////////////////////////////////////
		/////////////////////abstraction////////////////////////////////////////////////////////////////
		PrintWriter writer;
		try {
			//should also the corresponding kept node from the other trace be add?
			
			writer = new PrintWriter(proPath+"/results/Explainations.gv", "UTF-8");
			writer.println("digraph dualGraph {");
			writer.println("rankdir = BT;");
			writer.println("splines=ortho;");
			
	//		Collections.sort(old_visited, new TraceNodeOrderComparator());
	//		Collections.sort(new_visited, new TraceNodeOrderComparator());
						
			List<TraceNode> new_dat_kept = new ArrayList<>();
			List<TraceNode> old_dat_kept = new ArrayList<>();
			
			HashMap<TraceNode, Integer> old_data_node_function = new HashMap<>();
			HashMap<TraceNode, Integer> new_data_node_function = new HashMap<>();
			HashMap<TraceNode, Integer> old_ctl_node_function = new HashMap<>();
			HashMap<TraceNode, Integer> new_ctl_node_function = new HashMap<>();
			Integer index = 0;
			////////////////////////////////////First Define what to keep////////////////////////////////////////////////
			for(int i=old_visited.size()-1;i>=0; i--){
				TraceNode step = old_visited.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);				
				String Type;
				//System.out.println("on old " + step + " "+ changeType.toString());
				if(changeType.getType()==StepChangeType.DAT && !isATestStatement(tc, step)) {
					old_data_node_function.put(step, index);
					TraceNode matchedStep = changeType.getMatchingStep();	
					new_data_node_function.put(matchedStep, index);
					index = index + 1;
					if(old_kept.contains(step)) {//should be added but abstracted
						if(!new_dat_kept.contains(matchedStep))
							new_dat_kept.add(matchedStep);
					}					
				}
				else if (changeType.getType()==StepChangeType.CTL && !isATestStatement(tc, step)) {
					old_ctl_node_function.put(step, index);
					index = index + 1;
				}
				else {//it is retain
					if(!old_retained.contains(step))
						old_retained.add(step);
					if(!old_kept.contains(step))
						old_kept.add(step);
				}
				List<Pair<TraceNode, String>> data_deps = old_data_map.get(step);				
				if(data_deps!=null) 
					for(Pair<TraceNode, String> pair:data_deps) 
						if(old_visited.contains(pair.first()))
							if(oldBlocks.get(pair.first())!=oldBlocks.get(step))//keep the dep
								if(!old_kept.contains(pair.first()))
									old_kept.add(pair.first());
				
	//			List<TraceNode> ctl_deps = old_ctl_map.get(step);
	//			if(ctl_deps!=null) 
	//				for(TraceNode node:ctl_deps) 
	//					if(old_visited.contains(node))
	//						if(oldBlocks.get(node)!=oldBlocks.get(step))//keep the dep
	//							if(!old_kept.contains(node))
	//								old_kept.add(node);		
			}
			/////////////////////////////////////First Define what to keep///////////////////////////////////////////////
			for(int i=new_visited.size()-1;i>=0; i--){
				TraceNode step = new_visited.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);				
				String Type;				
				if(changeType.getType()==StepChangeType.DAT && !isATestStatement(tc, step)) {
					if (!new_data_node_function.keySet().contains(step)) {
						new_data_node_function.put(step, index);
						TraceNode matchedStep = changeType.getMatchingStep();	
						old_data_node_function.put(matchedStep, index);
						index = index + 1;
					}
					if (new_kept.contains(step)) {//should be added but abstracted
						TraceNode matchedStep = changeType.getMatchingStep();	
						if(!old_dat_kept.contains(matchedStep))
							old_dat_kept.add(matchedStep);
					}					
				}
				else if (changeType.getType()==StepChangeType.CTL && !isATestStatement(tc, step)) {
					new_ctl_node_function.put(step, index);
					index = index + 1;
				}
				else {				
					if(!new_retained.contains(step)) {				
						new_retained.add(step);
					}
					if(!new_kept.contains(step)) {
						new_kept.add(step);
					}
				}
				List<Pair<TraceNode, String>> data_deps = new_data_map.get(step);				
				if(data_deps!=null) 
					for(Pair<TraceNode, String> pair:data_deps) 
						if(new_visited.contains(pair.first()))
							if(newBlocks.get(pair.first())!=newBlocks.get(step))//keep the dep
								if(!new_kept.contains(pair.first()))
									new_kept.add(pair.first());
				
	//			List<TraceNode> ctl_deps = new_ctl_map.get(step);
	//			if(ctl_deps!=null) 
	//				for(TraceNode node:ctl_deps) 
	//					if(new_visited.contains(node))
	//						if(newBlocks.get(node)!=newBlocks.get(step))//keep the dep
	//							if(!new_kept.contains(node))
	//								new_kept.add(node);		
			}
			/////////////////////////////////////////////////////////////
	/////////////////////////////////////////////////////////////
	//Add test statements becasue they are in the dual slice//////
			for(TraceNode n: old_dat_kept) {
				if(!old_kept.contains(n)) {
				  old_kept.add(n);
				  }
			}
			for(TraceNode n: new_dat_kept) {
				if(!new_kept.contains(n)) {
				  new_kept.add(n);
				}
			}
	//		Collections.sort(old_visited, new TraceNodeOrderComparator());
	//		Collections.sort(new_visited, new TraceNodeOrderComparator());
			Collections.sort(old_kept, new TraceNodeOrderComparator());
			Collections.sort(new_kept, new TraceNodeOrderComparator());
			////////////////////////add nodes of old with abstraction/////////////////////
			PrintWriter fileWriter = new PrintWriter(proPath + "/results/old/inPreSS.txt", "UTF-8");		
			writer.println("subgraph cluster0 {");
			writer.println("color=black;");
			writer.println("label = \"old slice\";");
			for(int i=old_kept.size()-1;i>=0; i--){
				TraceNode step = old_kept.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, false, pairList, matcher);
				String Type;
				if(changeType.getType()==StepChangeType.DAT && !isATestStatement(tc, step)) {
					//if (old_kept.contains(step) || old_dat_kept.contains(step)) {//should be added but abstracted					
						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";
						List<VarValue> written = step.getWrittenVariables();
						List<String> vars = new ArrayList<>(); 
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited,step,vars,old_data_map,oldBlocks,old_kept, old_dat_kept);
						}
						catch (StackOverflowError e) {
					        System.err.println("oche!");
					    }
						String abstraction = "";
						if (written!=null && written.size()!=0 ) { //is an assignment
							abstraction = written.get(0).getVarName();
							abstraction = abstraction + "=Func_"+old_data_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
						}					
						else {
							abstraction = abstraction + "Func_"+old_data_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							
						}
						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";					
						String fixNode = step.toString();	
						writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");										
						fileWriter.println(abstraction);
									
				}
				else if (changeType.getType()==StepChangeType.CTL && !isATestStatement(tc, step)) {
					//if (old_kept.contains(step)) {//should be added but abstracted					
						Type= "color=blue fillcolor=lightskyblue1 shape=box style=filled fontsize=10";
						List<VarValue> written = step.getWrittenVariables();					
						List<String> vars = new ArrayList<>(); 
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited,step,vars,old_data_map,oldBlocks,old_kept, old_dat_kept);
						}
						catch (StackOverflowError e) {
					        System.err.println("oche!");
					    }
						String abstraction = "";
						if (written!=null && written.size()!=0) { //is an assignment
							abstraction = written.get(0).getVarName();
							abstraction = abstraction + "=Func_"+old_ctl_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							String fixNode = step.toString();	
							writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");
						}
						else {
							abstraction = abstraction + "Func_"+old_ctl_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							String fixNode = step.toString();	
							writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");
							//abstraction = getSourceCode(step, false, matcher, oldSlicer4J, oldSlicer4JBytecodeMapping);							
						}
						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";
						String fixNode = step.toString();	
						writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");
						fileWriter.println(abstraction);										
					
				}
				else {//retained set 				
					if (changeType.getType()==StepChangeType.SRCDAT || i==old_visited.size()-1) 
						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";					 									
					else if (changeType.getType()==StepChangeType.SRCCTL) 
						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";					
					else //(changeType.getType()==StepChangeType.IDT)
						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";					
					String fixNode = step.toString();			
					writer.println("\"OldNode: "+fixNode +"\""+ "["+Type+ " label=\""+getSourceCode(step, false, matcher)+"\"];");										
					fileWriter.println(getSourceCode(step, false, matcher));//add the node itself
				}	
			}
			writer.println("}");	
			fileWriter.close();
			/////////////////////////////////////////////////////////////
			////////////////////////add nodes of new/////////////////////
			fileWriter = new PrintWriter(proPath + "/results/new/inPreSS.txt", "UTF-8");
			writer.println("subgraph cluster1 {");
			writer.println("color=black;");
			writer.println("label = \"newslice\";");
			for(int i=new_kept.size()-1;i>=0; i--){
				TraceNode step = new_kept.get(i);
				StepChangeType changeType = typeChecker.getTypeForPrinting(step, true, pairList, matcher);
				String Type;
				if(changeType.getType()==StepChangeType.DAT && !isATestStatement(tc, step)) {
					//if (new_kept.contains(step) || new_dat_kept.contains(step)) {//should be added but abstracted
						//ABSTRACTION 						
						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";
						List<VarValue> written = step.getWrittenVariables();
						List<String> vars = new ArrayList<>(); 
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited, step,vars,new_data_map,newBlocks,new_kept, new_dat_kept);
						}
						catch (StackOverflowError e) {
					        System.err.println("oche!");
					    }
						String abstraction = "";
						if (written!=null&& written.size()!=0) { //is an assignment
							abstraction = written.get(0).getVarName();
							abstraction = abstraction + "=Func_"+new_data_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
						}
						else {
							abstraction = abstraction + "Func_"+new_data_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							//abstraction = getSourceCode(step, true, matcher, newSlicer4J, newSlicer4JBytecodeMapping);
						}
						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";					
						String fixNode = step.toString();	
						writer.println("\"NewNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");										
						fileWriter.println(abstraction);
					
				}
				else if (changeType.getType()==StepChangeType.CTL && !isATestStatement(tc, step)) {
					if (new_kept.contains(step)) {//should be added but abstracted					
						Type= "color=blue fillcolor=lightskyblue1 shape=box style=filled fontsize=10";
						List<VarValue> written = step.getWrittenVariables();
						List<ValueBox> writtenSoot = new ArrayList<>();
						List<String> vars = new ArrayList<>(); 
						List<TraceNode> visited = new ArrayList<>();
						try {
							visited.add(step);
							List<Pair<TraceNode, String>> temp = addVariable(visited,step,vars,new_data_map,newBlocks,new_kept, new_dat_kept);
						}
						catch (StackOverflowError e) {
					        System.err.println("oche!");
					    }
						String abstraction = "";
						if (written!=null && written.size()!=0) { //is an assignment
							abstraction = written.get(0).getVarName();
							abstraction = abstraction + "Func_"+new_ctl_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
						}
						else if (writtenSoot.size()!=0){
							abstraction = writtenSoot.get(0).getValue().toString();
							abstraction = abstraction + "=Func_"+new_ctl_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
						}
						else {
							abstraction = abstraction + "=Func_"+new_ctl_node_function.get(step)+"(";
							for(int j=0; j<vars.size();j++) {
								if(j!=vars.size()-1)
									abstraction = abstraction + vars.get(j) + ", ";
								else
									abstraction = abstraction + vars.get(j);
							}
							abstraction = abstraction + ");";
							//abstraction = getSourceCode(step, true, matcher, newSlicer4J, newSlicer4JBytecodeMapping);
						}
						Type= "color=orange fillcolor=orange2 shape=box style=filled fontsize=10";
						String fixNode = step.toString();	
						writer.println("\"NewNode: "+fixNode +"\""+ "["+Type+ " label=\""+abstraction+"\"];");										
						fileWriter.println(abstraction);
					}
				}
				else {//retained set 
					if (changeType.getType()==StepChangeType.SRCDAT || i==new_visited.size()-1) 
						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";					 
					else if (changeType.getType()==StepChangeType.SRCCTL) 
						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";
					else //(changeType.getType()==StepChangeType.IDT)
						Type = "color=red fillcolor=white shape=box style=filled fontsize=10";
					String fixNode = step.toString();			
					writer.println("\"NewNode: "+fixNode +"\""+ "["+Type+ " label=\""+getSourceCode(step, true, matcher)+"\"];");										
					fileWriter.println(getSourceCode(step, true, matcher));
				}
			}
			writer.println("}");
			fileWriter.close();
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			/////////////////////////add control flow edges//////////////
	//		Collections.sort(old_kept, new TraceNodeOrderComparator());
	//		Collections.sort(new_kept, new TraceNodeOrderComparator());
			
			for(int i=0;i<old_kept.size(); i++) {
				if(i!=old_kept.size()-1) {
					TraceNode step = old_kept.get(i);
					TraceNode BeforeStep = old_kept.get(i+1);
					writer.println("\"OldNode: "+BeforeStep +"\" " + "->" + "\"OldNode: "+step +"\" [color=gray55 style=dotted arrowhead=normal dir=back];");
				}
			}
			for(int i=0;i<new_kept.size(); i++) {
				if(i!=new_kept.size()-1) {
					TraceNode step = new_kept.get(i);
					TraceNode BeforeStep = new_kept.get(i+1);
					writer.println("\"NewNode: "+BeforeStep +"\" " + "->" + "\"NewNode: "+step +"\" [color=gray55 style=dotted arrowhead=normal dir=back] ;");
				}
			}
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			/////////////////////////add alignment edges//////////////////////////////////////////////////////////////////////////////
			for(int i=0;i<old_kept.size(); i++) {
				TraceNode step = old_kept.get(i);
				StepChangeType changeType = typeChecker.getType(step, false, pairList, matcher);
				TraceNode matchedStep = changeType.getMatchingStep();
				if(new_kept.contains(matchedStep)) {										
					writer.println("\"OldNode: "+step +"\" " + "->" + "\"NewNode: "+matchedStep +"\" [color=grey55 style=dotted arrowhead=none constraint=false];");
				}
			}
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			/////////////////////////add dependency edges////////////////
	//		for(int i=0;i<old_kept.size(); i++) {
	//			TraceNode step = old_kept.get(i);
	//			if(old_data_map.keySet().contains(step)) 
	//				if(old_data_map.get(step)!=null)
	//					for(Pair<TraceNode, String> dep: old_data_map.get(step)) 
	//						if(old_kept.contains(dep.first())) 		
	//							//if (!dep.second().contains("stack"))
	//								writer.println("\"OldNode: "+step +"\" " + "-> " + "\"OldNode: "+dep.first() +"\" [color=black style=solid arrowhead=normal constraint=false xlabel=\" "+dep.second() +"   \" ];");//connect data nodes to east					
	//			if(old_ctl_map.keySet().contains(step)) 
	//				if(old_ctl_map.get(step)!=null)
	//					for(TraceNode dep: old_ctl_map.get(step)) 
	//						if(old_kept.contains(dep)) 						
	//							writer.println("\"OldNode: "+step +"\" " + "-> " + "\"OldNode: "+dep +"\" [color=black style=dashed arrowhead=normal constraint=false];");//connect data nodes to west	
	//		}
	//		
	//		for(int i=0;i<new_kept.size(); i++) {
	//			TraceNode step = new_kept.get(i);
	//			if(new_data_map.keySet().contains(step)) 
	//				if(new_data_map.get(step)!=null)
	//					for(Pair<TraceNode, String> dep: new_data_map.get(step)) 
	//						if(new_kept.contains(dep.first())) 
	//							//if (!dep.second().contains("stack"))
	//								writer.println("\"NewNode: "+step +"\" " + "-> " + "\"NewNode: "+dep.first() +"\" [color=black style=solid arrowhead=normal constraint=false xlabel=\" "+dep.second() +"   \" ];");
	//			if(new_ctl_map.keySet().contains(step)) 
	//				if(new_ctl_map.get(step)!=null)
	//					for(TraceNode dep: new_ctl_map.get(step)) 
	//						if(new_kept.contains(dep)) 
	//							writer.println("\"NewNode: "+step +"\" " + "-> " + "\"NewNode: "+dep +"\" [color=black style=dashed arrowhead=normal constraint=false];");
	//		}
	
			/////////////////////////////////////////////////////////////////////
			writer.println("}");
			writer.close();
			
		} catch (FileNotFoundException e) {                                        
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
	
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private boolean isATestStatement(TestCase tc, TraceNode step) {
		String ClassName = step.getClassCanonicalName();
		if (tc.testClass.equals(ClassName)) {
			return true;
		}
		return false;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private List<Pair<TraceNode, String>> addVariable(List<TraceNode> visited, TraceNode step, List<String> vars, HashMap<TraceNode, List<Pair<TraceNode, String>>> data_map, HashMap<TraceNode, Integer> Blocks, List<TraceNode> kept, List<TraceNode> forced_kept) {
		//System.out.println("Node is " + step);
		List<Pair<TraceNode, String>> data_deps = data_map.get(step);	
		//System.out.println("the current is " + data_deps);
		List<Pair<TraceNode, String>> UpdatedDataDeps = new ArrayList<>();
		if(data_deps!=null) {
			for(Pair<TraceNode, String> pair:data_deps) {
				//System.out.println("The dep node is " + pair.first());
				if(kept.contains(pair.first()) || forced_kept.contains(pair.first())){//it is already kept in the trace just add it to vars
					//System.out.println("The dep node is kept => continue");
					if(!vars.contains(pair.second())) {
						//System.out.println("The var to be added from kept " + pair.second());
						vars.add(pair.second());
					}
					continue;
				}
				if(data_map.containsKey(pair.first())) {
					for(Pair<TraceNode, String> depDepsPair : data_map.get(pair.first())) {
						if (!UpdatedDataDeps.contains(depDepsPair))
							UpdatedDataDeps.add(depDepsPair);
					}
				}
				if(Blocks.get(pair.first()) == Blocks.get(step)){ //abstract pair.first()	
					try {
						if(!visited.contains(pair.first())){
							visited.add(pair.first());
							if(vars.size()<20) {
								List<Pair<TraceNode, String>> temp = addVariable(visited, pair.first(), vars, data_map, Blocks, kept, forced_kept);
								UpdatedDataDeps.addAll(temp);
							}
						}
					}
					catch (StackOverflowError e) {
				        System.err.println("oche!");
				    }
				}
				else {//it will be kept when analyzing deps of step 
					if(!vars.contains(pair.second()))
						vars.add(pair.second());
				}				
			}
		}
		if(UpdatedDataDeps.size()!=0 && UpdatedDataDeps!=null) {
			for(Pair<TraceNode, String> pair:UpdatedDataDeps )
				if((!data_deps.contains(pair)) && vars.contains(pair.second()))
					data_deps.add(pair);
		}
	//	System.out.println("updated is " + data_deps);
		if (data_deps!=null)
			data_map.put(step, data_deps);
		return UpdatedDataDeps;		
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	public static void WriteToExcel(String ExcelFilePath, String[] RowData){
	    try {
	            FileInputStream myxls = new FileInputStream(ExcelFilePath);
	            XSSFWorkbook ExcelWorkbook = new XSSFWorkbook(myxls);
	            XSSFSheet worksheet = ExcelWorkbook.getSheetAt(0);
	            int lastRow=worksheet.getLastRowNum();
	            ++lastRow;
	            Row row = worksheet.createRow(lastRow);
	            for (int index = 0; index < RowData.length; index++) {
	                row.createCell(index).setCellValue(RowData[index]);
	            }
	            
	            myxls.close();
	
	            try(FileOutputStream output_file =new FileOutputStream(new File(ExcelFilePath))) {
	                ExcelWorkbook.write(output_file);
	            }
	            catch(Exception e){}
	    }
	    catch(Exception e){
	    }
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	private void PrintFinalResultAll(TestCase tc, String basePath, String projectName, String bugID, Trace newTrace, Trace oldTrace, 
			List<TraceNode> new_visited, List<TraceNode> old_visited, List<TraceNode> new_kept, List<TraceNode> old_kept, 
			List<TraceNode> new_retained, List<TraceNode> old_retained, HashMap<Integer, List<TraceNode>> newDataBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldDataBlockNodes, HashMap<Integer, List<TraceNode>> newCtlBlockNodes, 
			HashMap<Integer, List<TraceNode>> oldCtlBlockNodes, int oldTraceTime, int newTraceTime, int codeTime, 
			int traceTime, int dualTime, int inPreSSTime, HashMap<Integer, Integer> oldChangeChunkInfo, 
			HashMap<Integer, Integer> newChangeChunkInfo,HashMap<Integer, Integer> oldTestCaseChunkInfo, HashMap<Integer, Integer> newTestCaseChunkInfo, 
			HashMap<Integer, Integer> oldCommonChunkInfo, HashMap<Integer, Integer> newCommonChunkInfo,
			int oldRetainedTestRemovedByDual, int newRetainedTestRemovedByDual) {
		
		System.out.println("Old trace size is " + oldTrace.getExecutionList().size());
		System.out.println("New trace size is " + newTrace.getExecutionList().size());
		System.out.println("Old dual size is " + old_visited.size());
		System.out.println("New dual size is " + new_visited.size());
		System.out.println("Old retained size is " + old_retained.size());
		System.out.println("New retained size is " + new_retained.size());
		System.out.println("Old inPreSS size is " + old_kept.size());
		System.out.println("New inPreSS size is " + new_kept.size());
		
		int oldAllRetained = old_retained.size()-oldRetainedTestRemovedByDual;
		int newAllRetained = new_retained.size()-newRetainedTestRemovedByDual;
		int oldAllinPreSSRetained = old_kept.size() - oldRetainedTestRemovedByDual;
		int newAllinPreSSRetained = new_kept.size() - newRetainedTestRemovedByDual;
		System.out.println("Old retained size (removing test that are removed by DS) is " + oldAllRetained);
		System.out.println("New retained size (removing test that are removed by DS) is " + newAllRetained);
		System.out.println("Old inPreSS size (removing test that are removed by DS) is " + oldAllinPreSSRetained);
		System.out.println("New inPreSS size (removing test that are removed by DS) is " + newAllinPreSSRetained);
		
	//	int OldTraceSourceSize = getTheSourceSize(oldTrace.getExecutionList());
	//	int NewTraceSourceSize = getTheSourceSize(newTrace.getExecutionList());
	//	int OldDualSourceSize = getTheSourceSize(old_visited);
	//	int NewDualSourceSize = getTheSourceSize(new_visited);
	//	int OldRetainedSourceSize = getTheSourceSize(old_retained);
	//	int NewRetainedSourceSize = getTheSourceSize(new_retained);
	//	int OldinPreSSSourceSize = getTheSourceSize(old_kept);
	//	int NewinPreSSSourceSize = getTheSourceSize(new_kept);
	//	
	//	System.out.println("Old trace size (source-level) is " + OldTraceSourceSize);
	//	System.out.println("New trace size (source-level) is " + NewTraceSourceSize);
	//	System.out.println("Old dual size (source-level) is " + OldDualSourceSize);
	//	System.out.println("New dual size (source-level) is " + NewDualSourceSize);
	//	System.out.println("Old retained size (source-level) is " + OldRetainedSourceSize);
	//	System.out.println("New retained size (source-level) is " + NewRetainedSourceSize);
	//	System.out.println("Old inPreSS size (source-level) is " + OldinPreSSSourceSize);
	//	System.out.println("New inPreSS size (source-level) is " + NewinPreSSSourceSize);
		
		System.out.println("Old #Data B is " + oldDataBlockNodes.keySet().size());
		System.out.println("New #Data B is " + newDataBlockNodes.keySet().size());
		System.out.println("Old #Control B is " + oldCtlBlockNodes.keySet().size());
		System.out.println("New #Control B is " + newCtlBlockNodes.keySet().size());
		System.out.println("old trace time is " + oldTraceTime);
		System.out.println("new trace time is " + newTraceTime);
		System.out.println("code diff " + codeTime);
		System.out.println("trace diff " + traceTime);
		System.out.println("dual time is " + dualTime);
		System.out.println("inPreSS time is " + inPreSSTime);
	    
		String results = basePath+"/results/"+projectName+".xlsx";
	    File tempFile = new File(results);
	    boolean FirstTime = false;
	    if (!tempFile.exists()) {//For the first time
	        FirstTime=true;
	        XSSFWorkbook workbook = new XSSFWorkbook();
	        XSSFSheet sheet = workbook.createSheet("stats");
	        try (FileOutputStream outputStream = new FileOutputStream(results)) {
	            workbook.write(outputStream);
	        } catch (Exception e) {
	        }
	    }
	
	    double sum = 0.0;
	    for(Integer loc:oldChangeChunkInfo.keySet()) {
	    	sum += oldChangeChunkInfo.get(loc);
	    }
	    double avg = sum/(double)oldChangeChunkInfo.keySet().size();
	    double oldLocation = avg/(double)oldTrace.getExecutionList().size();
	    int oldChangedStamts = getChanges(old_retained, tc);
	    
	    sum = 0.0;
	    for(Integer loc:newChangeChunkInfo.keySet()) {
	    	sum += newChangeChunkInfo.get(loc);
	    }
	    avg = sum/(double)newChangeChunkInfo.keySet().size();
	    double newLocation = avg/(double)newTrace.getExecutionList().size();
	    int newChangedStamts = getChanges(new_retained, tc);
	    	
	    double oldCommonBlockAvg = 0.0;
	    double oldCommonBlockMax = -1000000.0;
	    double oldCommonBlockMin = 100000.0;
	    double oldCommonBlockSum = 0.0;
		for (Integer blockID :oldCommonChunkInfo.keySet()) {
			Integer noOfStmts = oldCommonChunkInfo.get(blockID);
			if(noOfStmts!=null) {
				oldCommonBlockSum = oldCommonBlockSum + noOfStmts;
				if (oldCommonBlockMax<noOfStmts)
					oldCommonBlockMax = noOfStmts;
				if (oldCommonBlockMin>noOfStmts)
					oldCommonBlockMin = noOfStmts;
			}			
		}
		oldCommonBlockAvg = oldCommonBlockSum/oldCommonChunkInfo.keySet().size();
		System.out.println("Old Common block size (sum): " + oldCommonBlockSum);
		System.out.println("Old dCommon block size (avg) " + oldCommonBlockAvg);
		System.out.println("Old Common block size (min): " + oldCommonBlockMin);
		System.out.println("Old Common block size (max) " + oldCommonBlockMax);
		
	    double newCommonBlockAvg = 0.0;
	    double newCommonBlockMax = -1000000.0;
	    double newCommonBlockMin = 100000.0;
	    double newCommonBlockSum = 0.0;
		for (Integer blockID :newCommonChunkInfo.keySet()) {
			Integer noOfStmts = newCommonChunkInfo.get(blockID);
			if(noOfStmts!=null) {
				newCommonBlockSum = newCommonBlockSum + noOfStmts;
				if (newCommonBlockMax<noOfStmts)
					newCommonBlockMax = noOfStmts;
				if (newCommonBlockMin>noOfStmts)
					newCommonBlockMin = noOfStmts;
			}			
		}
		newCommonBlockAvg = newCommonBlockSum/newCommonChunkInfo.keySet().size();
		System.out.println("New Common block size (sum): " + newCommonBlockSum);
		System.out.println("New dCommon block size (avg) " + newCommonBlockAvg);
		System.out.println("New Common block size (min): " + newCommonBlockMin);
		System.out.println("New Common block size (max) " + newCommonBlockMax);
		
		//calculating #B, avg, max of data blocks on dual slice
	    double oldDATDualAvg = 0.0;
	    double oldDATDualMax = -1000000.0;
	    double oldDATDualMin = 100000.0;
	    double oldDATDualSum = 0.0;
		for (Integer block :oldDataBlockNodes.keySet()) {
			List<TraceNode> nodes = oldDataBlockNodes.get(block);
			if(nodes!=null) {
				oldDATDualSum = oldDATDualSum + nodes.size();
				if (oldDATDualMax<nodes.size())
					oldDATDualMax = nodes.size();
				if (oldDATDualMin>nodes.size())
					oldDATDualMin = nodes.size();
			}			
		}
		oldDATDualAvg = oldDATDualSum/oldDataBlockNodes.keySet().size();
		System.out.println("Old data dual block size (sum): " + oldDATDualSum);
		System.out.println("Old data dual block size (avg) " + oldDATDualAvg);
		System.out.println("Old data dual block size (min): " + oldDATDualMin);
		System.out.println("Old data dual block size (max) " + oldDATDualMax);
		
		double newDATDualAvg = 0.0;
	    double newDATDualMax = -100000.0;
	    double newDATDualMin = 100000.0;
	    double newDATDualSum = 0.0;
		for (Integer block :newDataBlockNodes.keySet()) {
			List<TraceNode> nodes = newDataBlockNodes.get(block);
			if(nodes!=null) {
				newDATDualSum = newDATDualSum + nodes.size();
				if (newDATDualMax<nodes.size())
					newDATDualMax = nodes.size();
				if (newDATDualMin>nodes.size())
					newDATDualMin = nodes.size();
			}			
		}
		newDATDualAvg = newDATDualSum/newDataBlockNodes.keySet().size();
		System.out.println("New data dual block size (sum): " + newDATDualSum);
		System.out.println("New data dual block size (avg) " + newDATDualAvg);
		System.out.println("New data dual block size (min): " + newDATDualMin);
		System.out.println("New data dual block size (max) " + newDATDualMax);
		
		//calculating #B, avg, max of data blocks on dual slice
		double oldDATinPreSSAvg = 0.0;
		double oldDATinPreSSMax = -100000.0;
		double oldDATinPreSSMin = 100000.0;
		double oldDATinPreSSSum = 0.0;
		for (Integer block :oldDataBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = oldDataBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (old_kept.contains(node))
						size = size + 1;
				}
				oldDATinPreSSSum = oldDATinPreSSSum + size;
				if (oldDATinPreSSMax<size)
					oldDATinPreSSMax = size;
				if (oldDATinPreSSMin>size)
					oldDATinPreSSMin = size;
			}			
		}
		oldDATinPreSSAvg = oldDATinPreSSSum/oldDataBlockNodes.keySet().size();
		System.out.println("Old data inPreSS block size (sum): " + oldDATinPreSSSum);
		System.out.println("Old data inPreSS block size (avg) " + oldDATinPreSSAvg);
		System.out.println("Old data inPreSS block size (min): " + oldDATinPreSSMin);
		System.out.println("Old data inPreSS block size (max) " + oldDATinPreSSMax);
		
		double newDATinPreSSAvg = 0.0;
	    double newDATinPreSSMax = -100000.0;
	    double newDATinPreSSMin = 100000.0;
	    double newDATinPreSSSum = 0.0;
		for (Integer block :newDataBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = newDataBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (new_kept.contains(node))
						size = size + 1;
				}
				newDATinPreSSSum = newDATinPreSSSum + size;
				if (newDATinPreSSMax<size)
					newDATinPreSSMax = size;
				if (newDATinPreSSMin>size)
					newDATinPreSSMin = size;
			}			
		}
		newDATinPreSSAvg = newDATinPreSSSum/newDataBlockNodes.keySet().size();
		System.out.println("New data inPreSS block size (sum): " + newDATinPreSSSum);
		System.out.println("New data inPreSS block size (avg) " + newDATinPreSSAvg);
		System.out.println("New data inPreSS block size (min): " + newDATinPreSSMin);
		System.out.println("New datat inPreSS block size (max) " + newDATinPreSSMax);
		
		///////////////////////////////
		double oldCTLDualAvg = 0.0;
		double oldCTLDualMax = -1000000.0;
		double oldCTLDualMin = 100000.0;
		double oldCTLDualSum = 0.0;
		for (Integer block :oldCtlBlockNodes.keySet()) {
			List<TraceNode> nodes = oldCtlBlockNodes.get(block);
			if(nodes!=null) {
				oldCTLDualSum = oldCTLDualSum + nodes.size();
				if (oldCTLDualMax<nodes.size())
					oldCTLDualMax = nodes.size();
				if (oldCTLDualMin>nodes.size())
					oldCTLDualMin = nodes.size();
			}			
		}
		oldCTLDualAvg = oldCTLDualSum/oldCtlBlockNodes.keySet().size();
		System.out.println("Old ctl dual block size (sum): " + oldCTLDualSum);
		System.out.println("Old ctl dual block size (avg) " + oldCTLDualAvg);
		System.out.println("Old ctl dual block size (min): " + oldCTLDualMin);
		System.out.println("Old ctl dual block size (max) " + oldCTLDualMax);
		
		double newCTLDualAvg = 0.0;
		double newCTLDualMax = -100000.0;
		double newCTLDualMin = 100000.0;
		double newCTLDualSum = 0.0;
		for (Integer block :newCtlBlockNodes.keySet()) {
			List<TraceNode> nodes = newCtlBlockNodes.get(block);
			if(nodes!=null) {
				newCTLDualSum = newCTLDualSum + nodes.size();
				if (newCTLDualMax<nodes.size())
					newCTLDualMax = nodes.size();
				if (newCTLDualMin>nodes.size())
					newCTLDualMin = nodes.size();
			}			
		}
		newCTLDualAvg = newCTLDualSum/newCtlBlockNodes.keySet().size();
		System.out.println("New ctl dual block size (sum): " + newCTLDualSum);
		System.out.println("New ctl dual block size (avg) " + newCTLDualAvg);
		System.out.println("New ctl dual block size (min): " + newCTLDualMin);
		System.out.println("New ctl dual block size (max) " + newCTLDualMax);
		
		//calculating #B, avg, max of data blocks on dual slice
		double oldCTLinPreSSAvg = 0.0;
		double oldCTLinPreSSMax = -100000.0;
		double oldCTLinPreSSMin = 100000.0;
		double oldCTLinPreSSSum = 0.0;
		for (Integer block :oldCtlBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = oldCtlBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (old_kept.contains(node))
						size = size + 1;
				}
				oldCTLinPreSSSum = oldCTLinPreSSSum + size;
				if (oldCTLinPreSSMax<size)
					oldCTLinPreSSMax = size;
				if (oldCTLinPreSSMin>size)
					oldCTLinPreSSMin = size;
			}			
		}
		oldCTLinPreSSAvg = oldCTLinPreSSSum/oldCtlBlockNodes.keySet().size();
		System.out.println("Old ctl inPreSS block size (sum): " + oldCTLinPreSSSum);
		System.out.println("Old ctl inPreSS block size (avg) " + oldCTLinPreSSAvg);
		System.out.println("Old ctl inPreSS block size (min): " + oldCTLinPreSSMin);
		System.out.println("Old ctl inPreSS block size (max) " + oldCTLinPreSSMax);
		
		double newCTLinPreSSAvg = 0.0;
	    double newCTLinPreSSMax = -100000.0;
	    double newCTLinPreSSMin = 100000.0;
	    double newCTLinPreSSSum = 0.0;
		for (Integer block :newCtlBlockNodes.keySet()) {
			int size = 0;
			List<TraceNode> nodes = newCtlBlockNodes.get(block);
			if(nodes!=null) {
				for (TraceNode node: nodes) {
					if (new_kept.contains(node))
						size = size + 1;
				}
				newCTLinPreSSSum = newCTLinPreSSSum + size;
				if (newCTLinPreSSMax<size)
					newCTLinPreSSMax = size;
				if (newCTLinPreSSMin>size)
					newCTLinPreSSMin = size;
			}			
		}
		newCTLinPreSSAvg = newCTLinPreSSSum/newCtlBlockNodes.keySet().size();
		System.out.println("New ctl inPreSS block size (sum): " + newCTLinPreSSSum);
		System.out.println("New ctl inPreSS block size (avg) " + newCTLinPreSSAvg);
		System.out.println("New ctl inPreSS block size (min): " + newCTLinPreSSMin);
		System.out.println("New ctl inPreSS block size (max) " + newCTLinPreSSMax);
		
	    if (FirstTime) {
	    	
	        String[] header = {"Bug ID", 
	        		"Old trace size", "New trace size", "Old Dual size", "New Dual size", 
	        		"Old No. Change Chunks", "Old Avg. Location of changes chunks in Trace", "Old No Changed Stmts", 
	        		"Old No. Test Chunks", "Old No. Test Stmts","old all retained size", "old all retained size (keeping all tests even not kept by DS)",
	        		"New No. Change Chunks", "New Avg. Location of changes chunks in Trace", "New No Changed Stmts", 
	        		"New No. Test Chunks", "New No. Test Stmts","new all retained size", "new all retained size (keeping all tests even not kept by DS)",
	        		"Old # Common B", "New # Common B",
	        		"old Common block (sum)","old Common block (avg)","old Common block (min)","old Common block (max)",
	        		"new Common block (sum)","new Common block (avg)","new Common block (min)","new Common block (max)",
	        		"Old ConSum size", "New ConSum size", 
	        		"Old ConSum size (keeping all tests even not kept by DS)", "New ConSum size (keeping all tests even not kept by DS)", 
	        		"Old #Data B", "New #Data B", "Old #Control B", "New #Control B", 
	        		 "old data block Dual (sum)","old data block Dual (avg)","old data block Dual (min)","old data block Dual (max)",
	        		 "new data block Dual (sum)","new data block Dual (avg)","new data block Dual (min)","new data block Dual (max)",
	        		 "old ctl block Dual (sum)","old ctl block Dual (avg)","old ctl block Dual (min)","old ctl block Dual (max)",
	        		 "new ctl block Dual (sum)","new ctl block Dual (avg)","new ctl block Dual (min)","new ctl block Dual (max)",
	        		 "old data block inPreSS (sum)","old data block inPreSS (avg)","old data block inPreSS (min)","old data block inPreSS (max)",
	        		 "new data block inPreSS (sum)","new data block inPreSS (avg)","new data block inPreSS (min)","new data block inPreSS (max)",
	        		 "old ctl block inPreSS (sum)","old ctl block inPreSS (avg)","old ctl block inPreSS (min)","old ctl block inPreSS (max)",
	        		 "new ctl block inPreSS (sum)","new ctl block inPreSS (avg)","new ctl block inPreSS (min)","new ctl block inPreSS (max)",
	        		 "old trace time", "new trace time", 
	        		 "code diff time", "trace diff time", "dual time", "inPreSS time" 
	        		 };
	        WriteToExcel(results, header);
	    }
	    String[] data = {bugID, 
	    		String.valueOf(oldTrace.getExecutionList().size()), String.valueOf(newTrace.getExecutionList().size()), 
	    		String.valueOf(old_visited.size()), String.valueOf(new_visited.size()), 
	    		String.valueOf(oldChangeChunkInfo.keySet().size()), String.valueOf(oldLocation), String.valueOf(oldChangedStamts),
	    		String.valueOf(oldTestCaseChunkInfo.keySet().size()), String.valueOf(old_retained.size()-oldChangedStamts), 
	    		String.valueOf(oldAllRetained), String.valueOf(old_retained.size()),
	    		String.valueOf(newChangeChunkInfo.keySet().size()), String.valueOf(newLocation), String.valueOf(newChangedStamts),
	    		String.valueOf(newTestCaseChunkInfo.keySet().size()), String.valueOf(new_retained.size()-newChangedStamts), 
	    		String.valueOf(newAllRetained), String.valueOf(new_retained.size()),
	    		String.valueOf(oldCommonChunkInfo.keySet().size()), String.valueOf(newCommonChunkInfo.keySet().size()),
	    		String.valueOf(oldCommonBlockSum),String.valueOf(oldCommonBlockAvg),String.valueOf(oldCommonBlockMin),String.valueOf(oldCommonBlockMax),
	    		String.valueOf(newCommonBlockSum),String.valueOf(newCommonBlockAvg),String.valueOf(newCommonBlockMin),String.valueOf(newCommonBlockMax),
	    		String.valueOf(oldAllinPreSSRetained), String.valueOf(newAllinPreSSRetained),
	    		String.valueOf(old_kept.size()), String.valueOf(new_kept.size()), 		
	    		String.valueOf(oldDataBlockNodes.keySet().size()), String.valueOf(newDataBlockNodes.keySet().size()),
	    		String.valueOf(oldCtlBlockNodes.keySet().size()), String.valueOf(newCtlBlockNodes.keySet().size()),
	    		String.valueOf(oldDATDualSum),String.valueOf(oldDATDualAvg),String.valueOf(oldDATDualMin),String.valueOf(oldDATDualMax),
	    		String.valueOf(newDATDualSum),String.valueOf(newDATDualAvg),String.valueOf(newDATDualMin),String.valueOf(newDATDualMax),
	    		String.valueOf(oldCTLDualSum),String.valueOf(oldCTLDualAvg),String.valueOf(oldCTLDualMin),String.valueOf(oldCTLDualMax),
	    		String.valueOf(newCTLDualSum),String.valueOf(newCTLDualAvg),String.valueOf(newCTLDualMin),String.valueOf(newCTLDualMax),
	    		String.valueOf(oldDATinPreSSSum),String.valueOf(oldDATinPreSSAvg),String.valueOf(oldDATinPreSSMin),String.valueOf(oldDATinPreSSMax),
	    		String.valueOf(newDATinPreSSSum),String.valueOf(newDATinPreSSAvg),String.valueOf(newDATinPreSSMin),String.valueOf(newDATinPreSSMax),
	    		String.valueOf(oldCTLinPreSSSum),String.valueOf(oldCTLinPreSSAvg),String.valueOf(oldCTLinPreSSMin),String.valueOf(oldCTLinPreSSMax),
	    		String.valueOf(newCTLinPreSSSum),String.valueOf(newCTLinPreSSAvg),String.valueOf(newCTLinPreSSMin),String.valueOf(newCTLinPreSSMax),
	    		String.valueOf(oldTraceTime),String.valueOf(newTraceTime),
	    		String.valueOf(codeTime), String.valueOf(traceTime), String.valueOf(dualTime),String.valueOf(inPreSSTime)
	    		};
	    WriteToExcel(results,data);
		
		
		System.out.println("##############Final Results##############");
		
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	/////////
	private int getChanges(List<TraceNode> retained, TestCase tc) {
		int no = 0;
		for (int i =0; i<=retained.size()-1; i++) {
			if (isATestStatement(tc,retained.get(i))) {
				//nothing
			}
			else {
				no++;
			}
		}
		return no;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	public Slicer setupSlicing(Path root, String jarPath, Path outDir, Path sliceLogger) {
		Slicer slicer = new Slicer();
		slicer.setPathJar(jarPath);
		slicer.setOutDir(outDir.toString());
		slicer.setLoggerJar(sliceLogger.toString());
	
		slicer.setFileToParse(outDir + File.separator + "trace.log");
		slicer.setStubDroidPath(
				root.getParent().toString() + File.separator + "models" + File.separator + "summariesManual");
		slicer.setTaintWrapperPath(root.getParent().toString() + File.separator + "models" + File.separator
				+ "EasyTaintWrapperSource.txt");
		return slicer;
	}
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////////////////////////
}
