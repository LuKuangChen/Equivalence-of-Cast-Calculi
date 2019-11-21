<TeXmacs|1.99.2>

<style|<tuple|generic|>>

<\body>
  <doc-data|<doc-title|A Framework for Equivalence of Cast
  Calculi>|<doc-author|<author-data|<author-name|Lu Kuang-Chen>>>>

  <section|Definitions>

  <\definition>
    <math|s\<approx\><rsup|\<ast\>>s<rprime|'>> if and only if there exists a
    state t such that <math|s\<longrightarrow\><rsup|\<ast\>>t> and
    <math|t\<approx\>s<rprime|'>>. Intuitively,
    <math|s\<approx\><rsup|\<ast\>>s<rprime|'>> means <math|s> will be
    related to <math|s<rprime|'>>.
  </definition>

  <\notation>
    <math|<around*|\<llbracket\>|c|\<rrbracket\>>> means
    <math|\<lambda\>V.applyCast<around*|(|V,c|)>>.
  </notation>

  <\lemma>
    If <math|U\<approx\>U<rprime|'>\<of\>A> then
    <math|<around*|\<llbracket\>|A\<Rightarrow\><rsup|l>B|\<rrbracket\>><around*|(|U|)>\<approx\><around*|\<llbracket\>|<around*|\<lceil\>|A\<Rightarrow\><rsup|l>B|\<rceil\>>|\<rrbracket\>><around*|(|U<rprime|'>|)>\<of\>B>.
  </lemma>

  <\definition>
    <math|extCont<around*|(|c,<around*|[|\<box\><around*|\<langle\>|d|\<rangle\>>|]>k|)>=<around*|[|\<box\><around*|\<langle\>|seq<around*|(|c,d|)>|\<rangle\>>|]>k>
  </definition>

  <\lemma>
    <math|extCont<around*|(|seq<around*|(|c,d|)>,\<kappa\>|)>=extCont<around*|(|c,extCont<around*|(|d,\<kappa\>|)>|)>>
  </lemma>

  <\lemma>
    If <math|\<kappa\>\<approx\>\<kappa\><rprime|'>> then
    <math|<around*|[|\<box\><around*|\<langle\>|A\<Rightarrow\><rsup|l>B|\<rangle\>>|]>\<kappa\>\<approx\>extCont<around*|(|<around*|\<lceil\>|A\<Rightarrow\><rsup|l>B|\<rceil\>>,\<kappa\><rprime|'>|)><rsup|*>>
  </lemma>

  <\lemma>
    For all <math|U\<approx\>U<rprime|'>> and <math|V\<approx\>V<rprime|'>>
    and <math|k\<approx\>k<rprime|'>> then
    <math|doApp<around*|(|U,V,\<kappa\>|)>\<approx\><rsup|\<star\>>doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>.
  </lemma>

  <\proof>
    By induction on <math|U\<approx\>U<rprime|'>>. There are two cases.

    <\indent>
      <with|font-series|bold|Case> <math|<around*|\<langle\>|\<lambda\>x\<of\>A\<point\>e\<of\>B,E|\<rangle\>>\<approx\><around*|\<langle\>|\<lambda\>x\<of\>id<around*|(|A|)>\<point\>e\<of\>id<around*|(|B|)>,E<rprime|'>|\<rangle\>>>

      In this case\ 

      <\eqnarray*>
        <tformat|<table|<row|<cell|>|<cell|>|<cell|doApp<around*|(|U,V,k|)>>>|<row|<cell|>|<cell|=>|<cell|doApp<around*|(|<around*|\<langle\>|\<lambda\>x\<of\>A\<point\>e\<of\>B,E|\<rangle\>>\<nocomma\>,V,\<kappa\>|)>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<langle\>|e,E<around*|[|x\<leftarrow\>V|]>,\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|doApp<rprime|'><around*|(|<around*|\<langle\>|\<lambda\>x\<of\>id<around*|(|A|)>\<point\>e\<of\>id<around*|(|B|)>,E<rprime|'>|\<rangle\>>,V<rprime|'>,\<kappa\><rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|id<around*|(|A|)>|\<rrbracket\>><around*|(|V<rprime|'>|)>\<ggeq\>\<lambda\>V<rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>>|<row|<cell|<around*|(|\<star\>|)>>|<cell|=>|<cell|<underline|Just
        V<rprime|'>>\<ggeq\>\<lambda\>V<rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>>>>
      </eqnarray*>

      The step marked with <math|<around*|(|\<star\>|)>> follows from the
      basic property of <math|id<around*|(|\<cdot\>|)>>, that is

      <\equation*>
        <around*|\<llbracket\>|id<around*|(|A|)>|\<rrbracket\>><around*|(|V|)>=Just
        V
      </equation*>

      By definition, <math|<around*|\<langle\>|e,E<around*|[|x\<leftarrow\>V|]>,\<kappa\>|\<rangle\>>\<approx\><around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>.

      Thus <math|<around*|\<langle\>|e,E<around*|[|x\<leftarrow\>V|]>,\<kappa\>|\<rangle\>>\<approx\><rsup|\<ast\>><around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>.

      <with|font-series|bold|Case> <math|<around*|\<langle\>|U<rsub|1><around*|\<langle\>|A\<rightarrow\>B\<Rightarrow\><rsup|l>C\<rightarrow\>D|\<rangle\>>,E|\<rangle\>>\<approx\><around*|\<langle\>|\<lambda\>x\<of\>seq<around*|(|<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>,c|)>\<point\>e\<of\>seq<around*|(|d,<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>|)>,E<rprime|'>|\<rangle\>>>

      Let <math|U<rsub|1><rprime|'>=<around*|\<langle\>|\<lambda\>x<rsup|c,d>.e,E<rprime|'>|\<rangle\>>
      >, we also have <math|U<rsub|1>\<approx\>U<rsub|1><rsup|<rprime|'>>>.

      In this case,

      <\eqnarray*>
        <tformat|<table|<row|<cell|>|<cell|>|<cell|doApp<around*|(|U,V,k|)>>>|<row|<cell|>|<cell|=>|<cell|doApp<around*|(|<around*|\<langle\>|U<rsub|1><around*|\<langle\>|A\<rightarrow\>B\<Rightarrow\><rsup|l>C\<rightarrow\>D|\<rangle\>>,E|\<rangle\>>,V,k|)>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|<around*|\<llbracket\>|C\<Rightarrow\><rsup|l>A|\<rrbracket\>><around*|(|V|)>\<ggeq\>\<lambda\>V<rsub|1>.<around*|\<langle\>|V<rsub|1>,<around*|[|<around*|(|U<rsub|1>
        \<box\>|)>|]><around*|[|B\<Rightarrow\><rsup|l>D|]>\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,k<rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|doApp<rprime|'><around*|(|<around*|\<langle\>|\<lambda\>x\<of\>seq<around*|(|<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>,c|)>.e\<of\>seq<around*|(|d,<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>|)>,E<rprime|'>|\<rangle\>>,V<rprime|'>,k<rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|seq<around*|(|<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>,c|)>|\<rrbracket\>><around*|(|V<rprime|'>|)>\<ggeq\>\<lambda\>V<rsub|1><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|1><rprime|'>|]>,extCont<around*|(|seq<around*|(|d,<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>|)>,k<rprime|'>|)>|\<rangle\>>>>|<row|<cell|<around*|(|\<star\>|)>>|<cell|=>|<cell|<underline|<around*|\<llbracket\>|<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>|\<rrbracket\>><around*|(|V<rprime|'>|)>\<ggeq\><around*|\<llbracket\>|c|\<rrbracket\>>>\<ggeq\>\<lambda\>V<rsub|1><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|1><rprime|'>|]>,extCont<around*|(|seq<around*|(|d,<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>|)>,k<rprime|'>|)>|\<rangle\>>>>>>
      </eqnarray*>

      The step marked with <math|<around*|(|\<star\>|)>> follows from the
      basic property of <math|seq<around*|(|\<cdot\>,\<cdot\>|)>>, that is

      <\equation*>
        <around*|\<llbracket\>|seq<around*|(|c,d|)>|\<rrbracket\>><around*|(|V|)>=<around*|\<llbracket\>|c|\<rrbracket\>><around*|(|V|)>\<ggeq\><around*|\<llbracket\>|d|\<rrbracket\>>
      </equation*>

      By Lemma 3, we can case-split <math|<around*|\<llbracket\>|C\<Rightarrow\><rsup|l>A|\<rrbracket\>><around*|(|V|)>>
      and <math|<around*|\<llbracket\>|<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>|\<rrbracket\>><around*|(|V<rprime|'>|)>>
      at the same time.

      <\indent>
        <with|font-series|bold|Case> <math|<around*|\<llbracket\>|C\<Rightarrow\><rsup|l>A|\<rrbracket\>><around*|(|V|)>=Err
        l> and <math|<around*|\<llbracket\>|<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>|\<rrbracket\>><around*|(|V<rprime|'>|)>=Err
        l>

        In this case\ 

        <\eqnarray*>
          <tformat|<table|<row|<cell|>|<cell|>|<cell|doApp<around*|(|U,V,\<kappa\>|)>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|Err
          l\<ggeq\>\<lambda\>V<rsub|1>.<around*|\<langle\>|V<rsub|1>,<around*|[|<around*|(|U<rsub|1>
          \<box\>|)>|]><around*|[|B\<Rightarrow\><rsup|l>D|]>\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|Err
          l>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|Err
          l\<ggeq\><around*|\<llbracket\>|c|\<rrbracket\>>\<ggeq\>\<lambda\>V<rsub|1><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|1><rprime|'>|]>,extCont<around*|(|seq<around*|(|d,<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>|)>,k<rprime|'>|)>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|Err
          l>>>>
        </eqnarray*>

        By definition, <math|Err l\<approx\>Err l>.

        Thus <math|doApp<around*|(|U,V,\<kappa\>|)>\<approx\><rsup|\<ast\>>doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>.

        <with|font-series|bold|Case> <math|<around*|\<llbracket\>|C\<Rightarrow\><rsup|l>A|\<rrbracket\>><around*|(|V|)>=Just
        V<rsub|1>> and <math|<around*|\<llbracket\>|<around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>|\<rrbracket\>><around*|(|V<rprime|'>|)>=Just
        V<rsub|1><rprime|'>> and <math|V<rsub|1>\<approx\>V<rsub|1><rprime|'>>

        In this case

        <\eqnarray*>
          <tformat|<table|<row|<cell|>|<cell|>|<cell|doApp<around*|(|U,V,\<kappa\>|)>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|Just
          V<rsub|1>\<ggeq\>\<lambda\>V<rsub|1>.<around*|\<langle\>|V<rsub|1>,<around*|[|<around*|(|U<rsub|1>
          \<box\>|)>|]><around*|[|B\<Rightarrow\><rsup|l>D|]>\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|<around*|\<langle\>|V<rsub|1>,<around*|[|<around*|(|U<rsub|1>
          \<box\>|)>|]><around*|[|B\<Rightarrow\><rsup|l>D|]>\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|doApp<around*|(|U<rsub|1>,V<rsub|1>,<around*|[|\<box\><around*|\<langle\>|B\<Rightarrow\><rsup|l>D|\<rangle\>>|]>\<kappa\>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|Just
          V<rsub|1><rprime|'>\<ggeq\><around*|\<llbracket\>|c|\<rrbracket\>>\<ggeq\>\<lambda\>V<rsub|2><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|2><rprime|'>|]>,extCont<around*|(|seq<around*|(|d,<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>|)>,k<rprime|'>|)>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|c|\<rrbracket\>><around*|(|V<rsub|1><rprime|'>|)>\<ggeq\>\<lambda\>V<rsub|2><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|2><rprime|'>|]>,extCont<around*|(|seq<around*|(|d,<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>|)>,k<rprime|'>|)>|\<rangle\>>>>|<row|<cell|<around*|(|\<star\>|)>>|<cell|=>|<cell|<around*|\<llbracket\>|c|\<rrbracket\>><around*|(|V<rsub|1><rprime|'>|)>\<ggeq\>\<lambda\>V<rsub|2><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|2><rprime|'>|]>,<underline|extCont<around*|(|d,extCont<around*|(|<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>,\<kappa\><rprime|'>|)>|)>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|doApp<rprime|'><around*|(|<around*|\<langle\>|\<lambda\>x<rsup|c,d>.e,E<rprime|'>|\<rangle\>>,V<rsub|1><rprime|'>,extCont<around*|(|<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>,\<kappa\><rprime|'>|)>|)>>>|<row|<cell|>|<cell|=>|<cell|doApp<rprime|'><around*|(|U<rsub|1><rprime|'>,V<rsub|1><rprime|'>,extCont<around*|(|<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>,\<kappa\><rprime|'>|)>|)>>>>>
        </eqnarray*>

        The step marked with <math|<around*|(|\<star\>|)>> follows from Lemma
        5.\ 

        Now we can use the induction hypothesis two show that\ 

        <\equation*>
          doApp<around*|(|U<rsub|1>,V<rsub|1>,<around*|[|\<box\><around*|\<langle\>|B\<Rightarrow\><rsup|l>D|\<rangle\>>|]>\<kappa\>|)>\<approx\><rsup|\<ast\>>doApp<rprime|'><around*|(|U<rsub|1><rprime|'>,V<rsub|1><rprime|'>,extCont<around*|(|<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>,\<kappa\><rprime|'>|)>|)>
        </equation*>

        because <math|U<rsub|1>\<approx\>U<rsub|1><rprime|'>> and
        <math|V<rsub|1>\<approx\>V<rsub|1><rprime|'>> and, by Lemma 6,
        <math|<around*|[|\<box\><around*|\<langle\>|B\<Rightarrow\><rsup|l>D|\<rangle\>>|]>\<kappa\>\<approx\>extCont<around*|(|<around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>,\<kappa\><rprime|'>|)>>.

        Thus <math|doApp<around*|(|U,V,\<kappa\>|)>\<approx\><rsup|\<ast\>>doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>.
      </indent>
    </indent>

    \;
  </proof>
</body>

<initial|<\collection>
</collection>>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|1>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Definitions>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>