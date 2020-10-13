package Tree;

public interface ITreeClient2 {

    /*@ public normal_behaviour
      @ requires tree1 != tree2;
      @ requires \invariant_for(tree1);
      @ requires tree1.isUniform(0);
      @ requires tree1.value == 0;
      @ ensures tree1.isUniform(1);
      @ ensures tree2.getVal() == \old(tree2).getVal();
      @*/
    public void test(ITree2 tree1, ITree2 tree2);
}