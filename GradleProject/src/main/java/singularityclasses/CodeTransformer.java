package singularityclasses;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

public class CodeTransformer {

    public static String[][] translate(String[] originalFileContents, String[] originalFileNames, String[] originalFilePaths, String[] validInterfaceNames) {
        if (originalFileContents == null || validInterfaceNames == null) return null;

        List<String> validInterfaces = new ArrayList<>();
        List<String> validInterfacePaths = new ArrayList<>();
        List<String> validInterfaceNamesNew = new ArrayList<>();

        List<String> otherFiles = new ArrayList<>();
        List<String> otherFilesPaths = new ArrayList<>();
        List<String> otherFilesNames = new ArrayList<>();

        int index = 0;
        for (String content : originalFileContents) {
            boolean isValidInterface = false;
             for (String interfaceName : validInterfaceNames) {
                if (content.contains("interface " + interfaceName + " ")) {
                    validInterfaces.add(content);
                    validInterfaceNamesNew.add(originalFileNames[index]);
                    validInterfacePaths.add(originalFilePaths[index]);
                    isValidInterface = true;
                }
            }
            if (!isValidInterface) {
                otherFiles.add(content);
                otherFilesNames.add(originalFileNames[index]);
                otherFilesPaths.add(originalFilePaths[index]);
            }
            index++;
        }

        System.out.println("Valid interface names:");
        for (String s : validInterfaceNames) {
            System.out.println(s);
        }
        System.out.println("Other file names:");
        for (String s : otherFilesNames) {
            System.out.println(s);
        }
        System.out.println("Valid interface paths:");
        for (String s : validInterfacePaths) {
            System.out.println(s);
        }
        System.out.println("Other file paths");
        for (String s : otherFilesPaths) {
            System.out.println(s);
        }

        String[] resInterfaces = translateValidInterfaces(validInterfaces.toArray(new String[0]), validInterfaceNames);
        String[] resOther = translateOtherFiles(otherFiles.toArray(new String[0]), otherFilesNames.toArray(new String[0]), validInterfaceNames);

        //Return two arrays of strings, the one at outer index 0 contains the file contents, the
        //one at index 1 contains he paths to which they are supposed to be written.
        String[][] res = new String[2][originalFileContents.length];
        res[0] = Stream.of(resInterfaces, resOther).flatMap(Stream::of).toArray(String[]::new);
        res[1] = Stream.of(validInterfacePaths.toArray(new String[0]), otherFilesPaths.toArray(new String[0])).flatMap(Stream::of).toArray(String[]::new);
        return res;
    }

    /**
     * Translates clients with respect to a set of names of valid interfaces by replacing every reference
     * to a valid interface by the name of the transformed version of the interface (by appending a '2')
     */
    public static String[] translateOtherFiles(String[] contents, String[] names, String[] validInterfaceNames) {
        if (contents == null || validInterfaceNames == null) return null;
        System.out.println("Transforming " + contents.length + " client/s");

        String[] res = new String[contents.length];
        String client;
        for (int i = 0; i < contents.length; i++) {
            res[i] = contents[i];
            String interfaceName;
            boolean implementsValidInterface = false;
            for (String validInterfaceName : validInterfaceNames) {
                interfaceName = validInterfaceName;
                if (res[i] == null) {
                    System.out.println("CLIENT WAS NULL AT POS " + i);
                }
                if (res[i].contains("implements " + interfaceName + " ")) {
                    implementsValidInterface = true;
                    res[i] = res[i].replace("implements " + interfaceName + " ", "<TEMP REPLACE>");
                }
                res[i] = res[i].replaceAll(interfaceName + " ", interfaceName + "2 ")
                               .replace("<TEMP REPLACE>", "implements " + interfaceName + " ");
            }
            if (!implementsValidInterface) {
                int indexStartImplements = res[i].indexOf("implements") + 11;
                int indexEndsImplements = res[i].indexOf(" ", indexStartImplements);
                String implemented = res[i].substring(indexStartImplements, indexEndsImplements);
                res[i] = res[i].replaceAll("implements " + implemented + " ", "implements " + implemented + "2 ");
            }

            res[i] = res[i].replaceAll("class " + names[i] + " ", "class " + names[i] + "2 ")
                           .replaceAll("interface " + names[i] + " ", "interface " + names[i] + "2 ")
                           .replaceAll("public " + names[i] + "\\(", "public " + names[i] + "2(");
        }
        return res;
    }

    public static String[] translateValidInterfaces(String[] contents, String[] names) {
        if (contents == null || names == null) return null;
        System.out.println("Transforming " + contents.length + " interface/s");

        String[] res = new String[contents.length];
        String interf;
        for (int i = 0; i < contents.length; i++) {
            interf = contents[i];
            if (interf == null) {
                System.out.println("INTERFACE WAS NULL AT POS" + i + " FOR NAME " + names[i]);
            }
            res[i] = interf.replaceAll("\\\\locset footprint", "\\\\bigint footprint")
                           //.replaceAll(names[i],  names[i] + "2")
                           .replaceAll("\\\\new_elems_fresh\\(\\\\result\\.footprint\\)", "true")
                           .replaceAll("\\\\new_elems_fresh\\(footprint\\)", "true")
                           .replaceAll("\\\\dl_isolated_from\\(footprint, [a-z,A-Z]*\\)", "true")
                           .replaceAll("\\\\dl_isolated_from\\(footprint, \\\\result\\)", "true");

            for (String name : names) {
                res[i] = res[i].replaceAll(name + " ", name + "2 ");
            }
         }
        return res;
    }
}
