package singularityclasses;

import org.jmlspecs.openjml.JmlTree;

import java.nio.file.Paths;
import java.util.List;

public class Util {

    public static String[] getNames(List<JmlTree.JmlCompilationUnit> cus) {
        return cus.stream()
                .map(e -> e.getSourceFile().getName())
                .map(e -> Paths.get(e).getFileName().toString())
                .map(e -> e.substring(0, e.lastIndexOf(".")))
                .toArray(String[]::new);
    }

/*    public static String[] getFileNamesFromPaths(String[] paths) {
        String[] res = new String[paths.length];
        int i = 0;
        for (String path : paths) {
            res[i] = path.substring(path.lastIndexOf("\\") + 1, path.lastIndexOf(".") - 1);
        }
    }
 */

}
