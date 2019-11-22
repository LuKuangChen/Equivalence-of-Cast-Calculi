<TeXmacs|1.99.2>

<style|<tuple|generic||math-brackets|number-long-article>>

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
    <math|extCont<around*|(|c,<around*|[|\<box\><around*|\<langle\>|d|\<rangle\>>|]>k|)>=<around*|[|\<box\><around*|\<langle\>|c
    \<#2A3E\>d|\<rangle\>>|]>k>
  </definition>

  <\lemma>
    <math|extCont<around*|(|c \<#2A3E\> d,\<kappa\>|)>=extCont<around*|(|c,extCont<around*|(|d,\<kappa\>|)>|)>>
  </lemma>

  <\lemma>
    If <math|\<kappa\>\<approx\>\<kappa\><rprime|'>> then
    <math|<around*|[|\<box\><around*|\<langle\>|A\<Rightarrow\><rsup|l>B|\<rangle\>>|]>\<kappa\>\<approx\>extCont<around*|(|<around*|\<lceil\>|A\<Rightarrow\><rsup|l>B|\<rceil\>>,\<kappa\><rprime|'>|)><rsup|*>>
  </lemma>

  <\lemma>
    For all <math|U\<approx\>U<rprime|'>:S\<rightarrow\>T> and
    <math|V\<approx\>V<rprime|'>:S> and <math|k\<approx\>k<rprime|'>:T>

    <\equation*>
      doApp<around*|(|U,V,\<kappa\>|)>\<approx\><rsup|\<star\>>doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>
    </equation*>
  </lemma>

  <\proof>
    By induction on <math|U\<approx\>U<rprime|'>>. There are two cases.

    <\indent>
      <with|font-series|bold|Case> <math|<around*|\<langle\>|\<lambda\><around*|(|x\<of\>S|)>:T\<point\>e,E|\<rangle\>>\<approx\><around*|\<langle\>|\<lambda\><around*|(|x\<of\>id<around*|(|S|)>|)>:id<around*|(|T|)>\<point\>e,E<rprime|'>|\<rangle\>>>

      In this case\ 

      <\eqnarray*>
        <tformat|<table|<row|<cell|>|<cell|>|<cell|doApp<around*|(|U,V,k|)>>>|<row|<cell|>|<cell|=>|<cell|doApp<around*|(|<around*|\<langle\>|\<lambda\><around*|(|x\<of\>A|)>:B\<point\>e,E|\<rangle\>>\<nocomma\>,V,\<kappa\>|)>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<langle\>|e,E<around*|[|x\<leftarrow\>V|]>,\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|doApp<rprime|'><around*|(|<around*|\<langle\>|\<lambda\><around*|(|x\<of\>id<around*|(|A|)>|)>:id<around*|(|B|)>\<point\>e,E<rprime|'>|\<rangle\>>,V<rprime|'>,\<kappa\><rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|id<around*|(|A|)>|\<rrbracket\>><around*|(|V<rprime|'>|)>\<ggeq\>\<lambda\>V<rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>>|<row|<cell|<around*|(|\<star\>|)>>|<cell|=>|<cell|Just
        V<rprime|'>\<ggeq\>\<lambda\>V<rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>>>>
      </eqnarray*>

      The step marked with <math|<around*|(|\<star\>|)>> follows from the
      basic property of <math|id<around*|(|\<cdot\>|)>>

      <\equation*>
        <around*|\<llbracket\>|id<around*|(|T|)>|\<rrbracket\>>=Just
      </equation*>

      By definition, <math|<around*|\<langle\>|e,E<around*|[|x\<leftarrow\>V|]>,\<kappa\>|\<rangle\>>\<approx\><around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>.

      Thus <math|<around*|\<langle\>|e,E<around*|[|x\<leftarrow\>V|]>,\<kappa\>|\<rangle\>>\<approx\><rsup|\<ast\>><around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rprime|'>|]>,\<kappa\><rprime|'>|\<rangle\>>>.

      <with|font-series|bold|Case> <math|<around*|\<langle\>|U<rsub|1><around*|\<langle\>|S<rsub|1>\<rightarrow\>T<rsub|1>\<Rightarrow\><rsup|l>S\<rightarrow\>T|\<rangle\>>,E|\<rangle\>>\<approx\><around*|\<langle\>|\<lambda\><around*|(|x\<of\><around*|\<lceil\>|S\<Rightarrow\><rsup|l>S<rsub|1>|\<rceil\>>\<#2A3E\>
      c|)>\<of\><around*|(|d \<#2A3E\><around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>|)>\<point\>e,E<rprime|'>|\<rangle\>>>

      Let <math|U<rsub|1><rprime|'>=<around*|\<langle\>|\<lambda\>x<rsup|c,d>.e,E<rprime|'>|\<rangle\>>
      >, we also have <math|U<rsub|1>\<approx\>U<rsub|1><rsup|<rprime|'>>:S<rsub|1>\<rightarrow\>T<rsub|1>>.

      In this case,

      <\eqnarray*>
        <tformat|<table|<row|<cell|>|<cell|>|<cell|doApp<around*|(|U,V,\<kappa\>|)>>>|<row|<cell|>|<cell|=>|<cell|doApp<around*|(|<around*|\<langle\>|U<rsub|1><around*|\<langle\>|S<rsub|1>\<rightarrow\>T<rsub|1>\<Rightarrow\><rsup|l>S\<rightarrow\>T|\<rangle\>>,E|\<rangle\>>,V,\<kappa\>|)>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|<around*|\<llbracket\>|S\<Rightarrow\><rsup|l>S<rsub|1>|\<rrbracket\>><around*|(|V|)>\<ggeq\>\<lambda\>V<rsub|1>.<around*|\<langle\>|V<rsub|1>,<around*|[|<around*|(|U<rsub|1>
        \<box\>|)>|]><around*|[|\<box\><around*|\<langle\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rangle\>>|]>\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,k<rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|doApp<rprime|'><around*|(|<around*|\<langle\>|\<lambda\><around*|(|x\<of\><around*|\<lceil\>|C\<Rightarrow\><rsup|l>A|\<rceil\>>\<#2A3E\>c|)>\<of\><around*|(|d
        \<#2A3E\><around*|\<lceil\>|B\<Rightarrow\><rsup|l>D|\<rceil\>>|)>\<point\>e,E<rprime|'>|\<rangle\>>,V<rprime|'>,\<kappa\><rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<around*|\<lceil\>|S\<Rightarrow\><rsup|l>S<rsub|1>|\<rceil\>>\<#2A3E\>
        c|\<rrbracket\>><around*|(|V<rprime|'>|)>\<ggeq\>\<lambda\>V<rsub|1><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|1><rprime|'>|]>,extCont<around*|(|d
        \<#2A3E\><around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>,\<kappa\><rprime|'>|)>|\<rangle\>>>>|<row|<cell|<around*|(|\<star\>|)>>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|d|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<around*|\<lceil\>|S\<Rightarrow\><rsup|l>S<rsub|1>|\<rceil\>>|\<rrbracket\>>|)><around*|(|V<rprime|'>|)>\<ggeq\>\<lambda\>V<rsub|1><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|1><rprime|'>|]>,extCont<around*|(|d
        \<#2A3E\><around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>,\<kappa\><rprime|'>|)>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<around*|\<lceil\>|S\<Rightarrow\><rsup|l>S<rsub|1>|\<rceil\>>|\<rrbracket\>><around*|(|V<rprime|'>|)>\<ggeq\><around*|\<llbracket\>|d|\<rrbracket\>>\<ggeq\>\<lambda\>V<rsub|1><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|1><rprime|'>|]>,extCont<around*|(|d,extCont<around*|(|<around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>,\<kappa\><rprime|'>|)>|)>|\<rangle\>>>>>>
      </eqnarray*>

      The step marked with <math|<around*|(|\<star\>|)>> follows from the
      basic property of <math|seq<around*|(|\<cdot\>,\<cdot\>|)>>

      <\equation*>
        <around*|\<llbracket\>|c \<#2A3E\>d|\<rrbracket\>>=<around*|\<llbracket\>|d|\<rrbracket\>>\<circ\><around*|\<llbracket\>|c|\<rrbracket\>>
      </equation*>

      By Lemma 3, we can case-split <math|<around*|\<llbracket\>|S\<Rightarrow\><rsup|l>S<rsub|1>|\<rrbracket\>><around*|(|V|)>>
      and <math|<around*|\<llbracket\>|<around*|\<lceil\>|S\<Rightarrow\><rsup|l>S<rsub|1>|\<rceil\>>|\<rrbracket\>><around*|(|V<rprime|'>|)>>
      at the same time.

      <\indent>
        <with|font-series|bold|Case> <math|<around*|\<llbracket\>|S\<Rightarrow\><rsup|l>S<rsub|1>|\<rrbracket\>><around*|(|V|)>=Error
        l> and <math|<around*|\<llbracket\>|<around*|\<lceil\>|S\<Rightarrow\><rsup|l>S<rsub|1>|\<rceil\>>|\<rrbracket\>><around*|(|V<rprime|'>|)>=Error
        l>

        In this case\ 

        <\eqnarray*>
          <tformat|<table|<row|<cell|>|<cell|>|<cell|doApp<around*|(|U,V,\<kappa\>|)>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|Error
          l\<ggeq\>\<lambda\>V<rsub|1>.<around*|\<langle\>|V<rsub|1>,<around*|[|<around*|(|U<rsub|1>
          \<box\>|)>|]><around*|[|\<box\><around*|\<langle\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rangle\>>|]>\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|Error
          l>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|Error
          l\<ggeq\><around*|\<llbracket\>|c|\<rrbracket\>>\<ggeq\>\<lambda\>V<rsub|1><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|1><rprime|'>|]>,extCont<around*|(|d
          \<#2A3E\><around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>,\<kappa\><rprime|'>|)>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|Error
          l>>>>
        </eqnarray*>

        By definition, <math|Error l\<approx\>Error l>.

        Thus <math|doApp<around*|(|U,V,\<kappa\>|)>\<approx\><rsup|\<ast\>>doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>.

        <with|font-series|bold|Case> <math|<around*|\<llbracket\>|S\<Rightarrow\><rsup|l>S<rsub|1>|\<rrbracket\>><around*|(|V|)>=Just
        V<rsub|1>> and <math|<around*|\<llbracket\>|<around*|\<lceil\>|S\<Rightarrow\><rsup|l>S<rsub|1>|\<rceil\>>|\<rrbracket\>><around*|(|V<rprime|'>|)>=Just
        V<rsub|1><rprime|'>> and <math|V<rsub|1>\<approx\>V<rsub|1><rprime|'>:S<rsub|1>>

        In this case

        <\eqnarray*>
          <tformat|<table|<row|<cell|>|<cell|>|<cell|doApp<around*|(|U,V,\<kappa\>|)>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|Just
          V<rsub|1>\<ggeq\>\<lambda\>V<rsub|1>.<around*|\<langle\>|V<rsub|1>,<around*|[|<around*|(|U<rsub|1>
          \<box\>|)>|]><around*|[|\<box\><around*|\<langle\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rangle\>>|]>\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|<around*|\<langle\>|V<rsub|1>,<around*|[|<around*|(|U<rsub|1>
          \<box\>|)>|]><around*|[|\<box\><around*|\<langle\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rangle\>>|]>\<kappa\>|\<rangle\>>>>|<row|<cell|>|<cell|\<longrightarrow\>>|<cell|doApp<around*|(|U<rsub|1>,V<rsub|1>,<around*|[|\<box\><around*|\<langle\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rangle\>>|]>\<kappa\>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|>|<cell|>|<cell|doApp<rprime|'><around*|(|U<rprime|'>,V<rprime|'>,\<kappa\><rprime|'>|)>>>|<row|<cell|>|<cell|=>|<cell|Just
          V<rsub|1><rprime|'>\<ggeq\><around*|\<llbracket\>|c|\<rrbracket\>>\<ggeq\>\<lambda\>V<rsub|2><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|2><rprime|'>|]>,extCont<around*|(|d
          \<#2A3E\><around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>,\<kappa\><rprime|'>|)>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|c|\<rrbracket\>><around*|(|V<rsub|1><rprime|'>|)>\<ggeq\>\<lambda\>V<rsub|2><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|2><rprime|'>|]>,extCont<around*|(|d
          \<#2A3E\><around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>,\<kappa\><rprime|'>|)>|\<rangle\>>>>|<row|<cell|<around*|(|\<star\>|)>>|<cell|=>|<cell|<around*|\<llbracket\>|c|\<rrbracket\>><around*|(|V<rsub|1><rprime|'>|)>\<ggeq\>\<lambda\>V<rsub|2><rprime|'>.<around*|\<langle\>|e,E<rprime|'><around*|[|x\<leftarrow\>V<rsub|2><rprime|'>|]>,extCont<around*|(|d,extCont<around*|(|<around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>,\<kappa\><rprime|'>|)>|)>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|doApp<rprime|'><around*|(|<around*|\<langle\>|\<lambda\><around*|(|x\<of\>c|)>\<of\>d\<point\>e,E<rprime|'>|\<rangle\>>,V<rsub|1><rprime|'>,extCont<around*|(|<around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>,\<kappa\><rprime|'>|)>|)>>>|<row|<cell|>|<cell|=>|<cell|doApp<rprime|'><around*|(|U<rsub|1><rprime|'>,V<rsub|1><rprime|'>,extCont<around*|(|<around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>,\<kappa\><rprime|'>|)>|)>>>>>
        </eqnarray*>

        The step marked with <math|<around*|(|\<star\>|)>> follows from Lemma
        5.\ 

        Because <math|U<rsub|1>\<approx\>U<rsub|1><rprime|'>> and
        <math|V<rsub|1>\<approx\>V<rsub|1><rprime|'>> and, by Lemma 6,
        <math|<around*|[|\<box\><around*|\<langle\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rangle\>>|]>\<kappa\>\<approx\>extCont<around*|(|<around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>,\<kappa\><rprime|'>|)>>,
        now we can use the induction hypothesis too show that\ 

        <\equation*>
          doApp<around*|(|U<rsub|1>,V<rsub|1>,<around*|[|\<box\><around*|\<langle\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rangle\>>|]>\<kappa\>|)>\<approx\><rsup|\<ast\>>doApp<rprime|'><around*|(|U<rsub|1><rprime|'>,V<rsub|1><rprime|'>,extCont<around*|(|<around*|\<lceil\>|T<rsub|1>\<Rightarrow\><rsup|l>T|\<rceil\>>,\<kappa\><rprime|'>|)>|)>
        </equation*>

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