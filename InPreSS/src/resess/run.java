package resess;


import java.util.ArrayList;
import java.util.List;


public class run {

	public static void main(String[] args) {

		generateResults generatoror = new generateResults();
		
		//String basePath = "/Users/.../bug_repos/";
		String basePath = args[0];
		
		
		//String projectName = "InPreSS";
		String projectName = args[1];
		
		
		//String bugID = "2";	
		String bugID = args[2];	
		
		//String testcase = "com.google.javascript.jscomp.IntegrationTest::testIssue787"; //clousr(1)
		String testcase = args[3];
		
		String proPath = basePath + projectName + "/" + bugID;
		String buggyPath = proPath + "/bug";
		String fixPath = proPath + "/fix";

		System.out.println("working on the " + bugID + "th bug of " + projectName + " project.");
		projConfig config = projConfig.getD4JConfig(projectName, Integer.valueOf(bugID));	
		List<String> includedClassNames = new ArrayList<>();
		List<String> excludedClassNames = new ArrayList<>();
		generatoror.generateResult(basePath, projectName, bugID, proPath, buggyPath, fixPath, 
				true, true, true, 3, true, true, config, testcase, includedClassNames,excludedClassNames, config.EraseorDual);
	    return;

	}	

}
