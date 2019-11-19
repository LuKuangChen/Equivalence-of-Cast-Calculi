<TeXmacs|1.99.2>

<style|<tuple|generic|>>

<\body>
  <doc-data|<doc-title|A Framework for Equivalence of Cast
  Calculi>|<doc-author|<author-data|<author-name|Lu Kuang-Chen>>>>

  <section|Definitions>

  <\definition>
    <math|s\<approx\><rsup|\<ast\>>s<rprime|'>> if and only if there exists a
    state t such that s\<longrightarrow\><rsup|\<ast\>>t and
    <math|t\<approx\>s<rprime|'>>. Intuitively,
    <math|s\<approx\><rsup|\<ast\>>s<rprime|'>> means <math|s> will be
    related to <math|s<rprime|'>>.
  </definition>

  <\lemma>
    If <math|s\<approx\>s<rprime|'>> then
    <math|s\<approx\><rsup|\<ast\>>s<rprime|'>>.
  </lemma>

  <\lemma>
    If <math|s\<longrightarrow\>t> and <math|t\<approx\><rsup|\<ast\>>s<rprime|'>>
    then <math|s\<approx\><rsup|\<ast\>>s<rprime|'>>.
  </lemma>

  <\lemma>
    If <math|U\<approx\>U<rprime|'>\<of\>A> then
    <math|appC<around*|(|U,A<long-arrow|\<rubber-Rightarrow\>|l>B|)>\<approx\>appCt<rprime|'><around*|(|U,<around*|\<lceil\>|A<long-arrow|\<rubber-Rightarrow\>|l>B|\<rceil\>>|)>\<of\>B>.
  </lemma>

  <\definition>
    <math|extCont<around*|(|c,<around*|[|\<box\><around*|\<langle\>|d|\<rangle\>>|]>k|)>=<around*|[|\<box\><around*|\<langle\>|seq<around*|(|c,d|)>|\<rangle\>>|]>k>
  </definition>

  <\lemma>
    If <math|\<kappa\>\<approx\>\<kappa\><rprime|'>\<of\>A> then
    <math|<around*|[|\<box\><around*|\<langle\>|A\<Rightarrow\><rsup|l>B|\<rangle\>>|]>\<kappa\>\<approx\><rsup|\<ast\>>extCont<around*|(|<around*|\<lceil\>|A\<Rightarrow\><rsup|l>B|\<rceil\>>,\<kappa\><rprime|'>|)><rsup|*>>
  </lemma>

  <\lemma>
    For all <math|U\<approx\>U<rprime|'>\<of\>A\<rightarrow\>B> and
    <math|V\<approx\>V<rprime|'>\<of\>A> and
    <math|k\<approx\>k<rprime|'>\<of\>B> then
    <math|app<around*|(|U,V,\<kappa\>|)>\<approx\><rsup|\<ast\>>app<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>.
  </lemma>

  <\proof>
    By induction on <math|U\<approx\><rsup|CS>U<rprime|'>\<of\>\<Alpha\>\<rightarrow\>\<Beta\>>.
    There are two cases:

    <\indent>
      <with|font-series|bold|Case> <math|<around*|\<langle\>|\<lambda\>x<rsup|A,B>.e,E|\<rangle\>>\<approx\><around*|\<langle\>|\<lambda\>x<rsup|id<around*|(|A|)>,id<around*|(|B|)>>.e,E<rprime|'>|\<rangle\>>\<of\>A\<rightarrow\>B>

      In this case\ 

      <\itemize>
        <item><math|app<around*|(|U,V,k|)>=app<around*|(|<around*|\<langle\>|\<lambda\>x<rsup|A,B>.e,E|\<rangle\>>\<nocomma\>,V,\<kappa\>|)>=<around*|\<langle\>|e,E<around*|[|x\<leftarrow\>V|]>,\<kappa\>|\<rangle\>>>

        <item><math|app<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>=app<rprime|'><around*|(|<around*|\<langle\>|\<lambda\>x<rsup|id<around*|(|A|)>,id<around*|(|B|)>>.e,E<rprime|'>|\<rangle\>>,V<rprime|'>,\<kappa\><rprime|'>|)>=<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>
      </itemize>

      By the definition of our bisimulation relation
      <math|<around*|\<langle\>|e,E<around*|[|x\<leftarrow\>V|]>,\<kappa\>|\<rangle\>>\<approx\><around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>.

      By Lemma 2, <math|app<around*|(|U,V,\<kappa\>|)>\<approx\><rsup|\<ast\>>app<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>.

      <with|font-series|bold|Case> <math|<around*|\<langle\>|U<rsub|1><around*|\<langle\>|A\<rightarrow\>B\<Rightarrow\><rsup|l>C\<rightarrow\>D|\<rangle\>>,E|\<rangle\>>\<approx\><around*|\<langle\>|\<lambda\>x<rsup|seq<around*|(|<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>,c|)>,seq<around*|(|d,<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>|)>>.e,E<rprime|'>|\<rangle\>>\<of\>C\<rightarrow\>D>

      Let <math|U<rsub|1><rprime|'>=<around*|\<langle\>|\<lambda\>x<rsup|c,d>.e,E<rprime|'>|\<rangle\>>
      >, we also have <math|U<rsub|1>\<approx\>U<rsub|1><rsup|<rprime|'>>\<of\>A\<rightarrow\>B>.\ 

      The left state is <math|<around*|\<langle\>|V,<around*|[|\<box\><around*|\<langle\>|C\<Rightarrow\><rsup|l>A|\<rangle\>>|]><around*|[|<around*|(|U<rsub|1>
      \<box\>|)>|]><around*|[|B\<Rightarrow\><rsup|l>D|]>\<kappa\>|\<rangle\>>>,
      whose <with|font-shape|italic|next> state is\ 

      <\equation*>
        appC<around*|(|V,C\<Rightarrow\><rsup|l>A|)>\<ggeq\>\<lambda\>V<rsub|1>.<around*|\<langle\>|V,<around*|[|<around*|(|U<rsub|1>
        \<box\>|)>|]><around*|[|B\<Rightarrow\><rsup|l>D|]>\<kappa\>|\<rangle\>>
      </equation*>

      depends on the result of <math|appC<around*|(|V,C\<Rightarrow\><rsup|l>A|)>>.

      And the right state is (roughly)\ 

      <\equation*>
        appC<rprime|'><around*|(|V<rprime|'>\<nocomma\>,seq<around*|(|<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>,c|)>|)>\<ggeq\>\<lambda\>V<rsub|1><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|1><rprime|'>|]>,extCont<around*|(|seq<around*|(|d,<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>|)>,\<kappa\><rprime|'>|)>|\<rangle\>>
      </equation*>

      By the basic property of <math|seq<around*|(|\<cdot\>,\<cdot\>|)>>, we
      can apply <math|<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>>
      and <math|c> sequencely. So the right state can be re-written to

      <\equation*>
        appC<rprime|'><around*|(|V<rprime|'>,<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>|)>\<ggeq\>\<lambda\>V<rsub|1><rprime|'>.appC<rprime|'><around*|(|V<rsub|1><rprime|'>\<nocomma\>,c|)>\<ggeq\>\<lambda\>V<rsub|2><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|2><rprime|'>|]>,extCont<around*|(|seq<around*|(|d,<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>|)>,\<kappa\><rprime|'>|)>|\<rangle\>>
      </equation*>

      By Lemma 4, we can case-split <math|applyCast<around*|(|V,C\<Rightarrow\><rsup|l>A|)>>
      and <math|applyCast<rprime|'><around*|(|V<rprime|'>,<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>|)>>
      at the same time.

      <\indent>
        <with|font-series|bold|Case> <math|applyCast<around*|(|V,C<long-arrow|\<rubber-Rightarrow\>|l>A|)>=l>
        and <math|applyCast<rprime|'><around*|(|V<rprime|'>,<around*|\<lceil\>|C<long-arrow|\<rubber-Rightarrow\>|l>A|\<rceil\>>|)>=l>

        In this case\ 

        <\eqnarray*>
          <tformat|<table|<row|<cell|>|<cell|>|<cell|app<around*|(|U,V,\<kappa\>|)>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<langle\>|V,<around*|[|\<box\><around*|\<langle\>|C\<Rightarrow\><rsup|l>A|\<rangle\>>|]><around*|[|<around*|(|U<rsub|1>
          \<box\>|)>|]><around*|[|B\<Rightarrow\><rsup|l>D|]>\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|Halt
          l>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|app<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|Halt
          l>>>>
        </eqnarray*>

        The final states are related by definition.

        <with|font-series|bold|Case> <math|applyCast<around*|(|V,C<long-arrow|\<rubber-Rightarrow\>|l>A|)>=V<rsub|1>>
        and <math|applyCast<rprime|'><around*|(|V<rprime|'>,<around*|\<lceil\>|C<long-arrow|\<rubber-Rightarrow\>|l>A|\<rceil\>>|)>=V<rsub|1><rprime|'>>
        and <math|V<rsub|1>\<approx\>V<rsub|1><rprime|'>\<of\>C>

        In this case, the reduction at the left side is straightforward.

        <\eqnarray*>
          <tformat|<table|<row|<cell|>|<cell|>|<cell|app<around*|(|U,V,\<kappa\>|)>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<langle\>|V,<around*|[|\<box\><around*|\<langle\>|C\<Rightarrow\><rsup|l>A|\<rangle\>>|]><around*|[|U<rsub|1>
          \<box\>|]><around*|[|\<box\><around*|\<langle\>|B\<Rightarrow\><rsup|l>D|\<rangle\>>|]>\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|<around*|\<langle\>|V<rsub|1>,<around*|[|U<rsub|1>
          \<box\>|]><around*|[|\<box\><around*|\<langle\>|B\<Rightarrow\><rsup|l>D|\<rangle\>>|]>\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|app<around*|(|U<rsub|1>,V<rsub|1>,<around*|[|\<box\><around*|\<langle\>|B\<Rightarrow\><rsup|l>D|\<rangle\>>|]>\<kappa\>|)>>>>>
        </eqnarray*>

        The reduction at the right side is subtle.\ 

        The finial states\ 
      </indent>
    </indent>

    \;
  </proof>
</body>

<initial|<\collection>
</collection>>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|?>>
  </collection>
</references>