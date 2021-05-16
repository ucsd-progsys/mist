%%
%% This is file `darts-v2019.cls'.
%% 
%% -----------------------------------------------------------------
%% Author:     Dagstuhl Publishing & le-tex publishing services
%% 
%% This file is part of the darts package for preparing
%% DARTS articles.
%% 
%% Copyright (C) 2018 Schloss Dagstuhl
%%
%% This work may be distributed and/or modified under the
%% conditions of the LaTeX Project Public License, either version 1.3
%% of this license or (at your option) any later version.
%% The latest version of this license is in
%%   http://www.latex-project.org/lppl.txt
%% and version 1.3 or later is part of all distributions of LaTeX
%% version 2005/12/01 or later.
%%
%% This work has the LPPL maintenance status `maintained'.
%% 
%% The Current Maintainer of this work is 
%% Schloss Dagstuhl (publishing@dagstuhl.de).
%% -----------------------------------------------------------------
\ProvidesClass{darts-v2021}
    [2021/01/04 v3.1.0 DARTS articles]
\NeedsTeXFormat{LaTeX2e}[2015/01/01]
\emergencystretch1em
\advance\hoffset-1in
\advance\voffset-1in
\advance\hoffset2.95mm
\newif\if@nobotseplist  \@nobotseplistfalse
\def\@endparenv{%
  \addpenalty\@endparpenalty\if@nobotseplist\else\addvspace\@topsepadd\fi\@endpetrue}
\def\@doendpe{%
  \@endpetrue
  \def\par{\@restorepar
           \everypar{}%
           \par
           \if@nobotseplist
             \addvspace\topsep
             \addvspace\partopsep
             \global\@nobotseplistfalse
           \fi
           \@endpefalse}%
  \everypar{{\setbox\z@\lastbox}%
            \everypar{}%
            \if@nobotseplist\global\@nobotseplistfalse\fi
            \@endpefalse}}
\def\enumerate{%
  \ifnum \@enumdepth >\thr@@\@toodeep\else
    \advance\@enumdepth\@ne
    \edef\@enumctr{enum\romannumeral\the\@enumdepth}%
    \expandafter
    \list
      \csname label\@enumctr\endcsname
      {\advance\partopsep\topsep
       \topsep\z@\@plus\p@
       \ifnum\@listdepth=\@ne
         \labelsep0.72em
       \else
         \ifnum\@listdepth=\tw@
           \labelsep0.3em
         \else
           \labelsep0.5em
         \fi
       \fi
       \usecounter\@enumctr\def\makelabel##1{\hss\llap{##1}}}%
  \fi}
\def\endenumerate{\ifnum\@listdepth=\@ne\global\@nobotseplisttrue\fi\endlist}
\def\itemize{%
  \ifnum \@itemdepth >\thr@@\@toodeep\else
    \advance\@itemdepth\@ne
    \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
    \expandafter
    \list
      \csname\@itemitem\endcsname
      {\advance\partopsep\topsep
       \topsep\z@\@plus\p@
       \ifnum\@listdepth=\@ne
         \labelsep0.83em
       \else
         \ifnum\@listdepth=\tw@
           \labelsep0.75em
         \else
           \labelsep0.5em
         \fi
      \fi
      \def\makelabel##1{\hss\llap{##1}}}%
  \fi}
\def\enditemize{\ifnum\@listdepth=\@ne\global\@nobotseplisttrue\fi\endlist}
\def\@sect#1#2#3#4#5#6[#7]#8{%
  \ifnum #2>\c@secnumdepth
    \let\@svsec\@empty
  \else
    \refstepcounter{#1}%
    \protected@edef\@svsec{\@seccntformat{#1}\relax}%
  \fi
  \@tempskipa #5\relax
  \ifdim \@tempskipa>\z@
    \begingroup
      #6{%
        \@hangfrom{\hskip #3\relax
          \ifnum #2=1
            \colorbox{dartsYellow}{\kern0.15em\@svsec\kern0.15em}\quad
          \else
            \@svsec\quad
          \fi}%
          \interlinepenalty \@M #8\@@par}%
    \endgroup
    \csname #1mark\endcsname{#7}%
    \addcontentsline{toc}{#1}{%
      \ifnum #2>\c@secnumdepth \else
        \protect\numberline{\csname the#1\endcsname}%
      \fi
      #7}%
  \else
    \def\@svsechd{%
      #6{\hskip #3\relax
      \@svsec #8}%
      \csname #1mark\endcsname{#7}%
      \addcontentsline{toc}{#1}{%
        \ifnum #2>\c@secnumdepth \else
          \protect\numberline{\csname the#1\endcsname}%
        \fi
        #7}}%
  \fi
  \@xsect{#5}}
\def\@seccntformat#1{\csname the#1\endcsname}
\def\@biblabel#1{\textcolor{darkgray}{\sffamily\bfseries#1}}
\def\three@digits#1{\ifnum#1>99\else\ifnum#1>9 0\else00\fi\fi\number#1}
\def\copyrightline{%
  \scriptsize
  \vtop{\hsize\textwidth
    \nobreakspace\par
    \@Copyright
    \textit{Dagstuhl Artifacts Series}%
    \ifx\@Volume\@empty,\space Vol.\nobreakspace\textcolor{blue}{VOL}\else,\space Vol.\nobreakspace\@Volume\fi
    \ifx\@Issue\@empty,\space Issue\nobreakspace\textcolor{blue}{ISS}\else,\space Issue\nobreakspace\@Issue\fi
    \ifx\@Article\@empty,\space Artifact\nobreakspace{}No.\nobreakspace\textcolor{blue}{ART NO.}\else,\space Artifact\nobreakspace{}No.\nobreakspace\@Article\fi
    ,\space \ifx\@Article\@empty pp.\nobreakspace{}\textcolor{blue}{ART}:\thepage--\textcolor{blue}{ART}:\number\numexpr\getpagerefnumber{TotPages}\else pp.\nobreakspace{}\@Article:\thepage--\@Article:\number\numexpr\getpagerefnumber{TotPages}\fi\\
    \setbox\@tempboxa\hbox{\includegraphics[height=14\p@,trim=0 15 0 0]{darts-logo-bw}}%
    \hspace*{\wd\@tempboxa}\enskip
    \href{https://www.dagstuhl.de/darts}%
         {Dagstuhl Artifacts Series}\\
    \smash{\unhbox\@tempboxa}\enskip
    \href{https://www.dagstuhl.de}%
         {Schloss Dagstuhl -- Leibniz-Zentrum f{\"u}r Informatik, Dagstuhl Publishing, Germany}}}
\def\ps@plain{\let\@mkboth\@gobbletwo
  \let\@oddhead\@empty
  \let\@evenhead\@empty
  \let\@evenfoot\copyrightline
  \let\@oddfoot\copyrightline}
\def\darts@opterrshort{Option  "\CurrentOption" not supported}
\def\darts@opterrlong{The option "\CurrentOption" from article.cls is not supported by darts.cls.}
\DeclareOption{a5paper}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{b5paper}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{legalpaper}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{executivepaper}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{landscape}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{10pt}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{11pt}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{12pt}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{oneside}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{twoside}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{titlepage}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{notitlepage}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{onecolumn}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{twocolumn}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{fleqn}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{openbib}{\@latexerr{\darts@opterrshort}{\darts@opterrlong}}
\DeclareOption{pdfa}{\let\pdfa\relax}
\DeclareOption{a4paper}{\PassOptionsToClass{\CurrentOption}{article}
                        \advance\hoffset-2.95mm
                        \advance\voffset8.8mm}
\DeclareOption{numberwithinsect}{\let\numberwithinsect\relax}
\DeclareOption{anonymous}{\let\authoranonymous\relax}
\DeclareOption{authorcolumns}{\let\authorcolumns\relax}
\let\compactauthor\relax
\DeclareOption{oldauthorstyle}{\let\compactauthor\@empty}
\DeclareOption{compactauthor}{\let\compactauthor\relax}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions
\LoadClass[twoside,notitlepage,fleqn]{article}
\renewcommand\normalsize{%
   \@setfontsize\normalsize\@xpt{13}%
   \abovedisplayskip 10\p@ \@plus2\p@ \@minus5\p@
   \abovedisplayshortskip \z@ \@plus3\p@
   \belowdisplayshortskip 6\p@ \@plus3\p@ \@minus3\p@
   \belowdisplayskip \abovedisplayskip
   \let\@listi\@listI}
\normalsize
\renewcommand\small{%
   \@setfontsize\small\@ixpt{11.5}%
   \abovedisplayskip 8.5\p@ \@plus3\p@ \@minus4\p@
   \abovedisplayshortskip \z@ \@plus2\p@
   \belowdisplayshortskip 4\p@ \@plus2\p@ \@minus2\p@
   \def\@listi{\leftmargin\leftmargini
               \topsep 4\p@ \@plus2\p@ \@minus2\p@
               \parsep 2\p@ \@plus\p@ \@minus\p@
               \itemsep \parsep}%
   \belowdisplayskip \abovedisplayskip
}
\renewcommand\footnotesize{%
   \@setfontsize\footnotesize{8.5}{9.5}%
   \abovedisplayskip 6\p@ \@plus2\p@ \@minus4\p@
   \abovedisplayshortskip \z@ \@plus\p@
   \belowdisplayshortskip 3\p@ \@plus\p@ \@minus2\p@
   \def\@listi{\leftmargin\leftmargini
               \topsep 3\p@ \@plus\p@ \@minus\p@
               \parsep 2\p@ \@plus\p@ \@minus\p@
               \itemsep \parsep}%
   \belowdisplayskip \abovedisplayskip
}
\renewcommand\large{\@setfontsize\large{10.5}{13}}
\renewcommand\Large{\@setfontsize\Large{12}{14}}
\setlength\parindent{1.5em}
\setlength\headheight{3mm}
\setlength\headsep   {10mm}
\setlength\footskip{3mm}
\setlength\textwidth{148mm}%was 140
\setlength\textheight{222mm}
\setlength\oddsidemargin{28mm}%was 32
\setlength\evensidemargin{34mm}%was 38
\setlength\marginparwidth{25mm}
\setlength\topmargin{13mm}
\setlength{\skip\footins}{2\baselineskip \@plus 4\p@ \@minus 2\p@}
\def\@listi{\leftmargin\leftmargini
            \parsep\z@ \@plus\p@
            \topsep 8\p@ \@plus2\p@ \@minus4\p@
            \itemsep \parsep}
\let\@listI\@listi
\@listi
\def\@listii {\leftmargin\leftmarginii
              \labelwidth\leftmarginii
              \advance\labelwidth-\labelsep
              \topsep    4\p@ \@plus2\p@ \@minus\p@
              \parsep\z@ \@plus\p@
              \itemsep   \parsep}
\def\@listiii{\leftmargin\leftmarginiii
              \labelwidth\leftmarginiii
              \advance\labelwidth-\labelsep
              \topsep    2\p@ \@plus\p@\@minus\p@
              \parsep    \z@
              \partopsep \p@ \@plus\z@ \@minus\p@
              \itemsep   \z@ \@plus\p@}
\def\ps@headings{%
    \def\@evenhead{\large\sffamily\bfseries
                   \llap{\hbox to0.5\oddsidemargin{\ifx\@Article\@empty\textcolor{blue}{XX}\else\@Article\fi:\thepage\hss}}\leftmark\hfil}%
    \def\@oddhead{\large\sffamily\bfseries\rightmark\hfil
                  \rlap{\hbox to0.5\oddsidemargin{\hss\ifx\@Article\@empty\textcolor{blue}{XX}\else\@Article\fi:\thepage}}}%
    \def\@oddfoot{\hfil
                  \rlap{%
                    \vtop{%
                      \vskip10mm
                      \colorbox{dartsYellow}
                                    {\@tempdima\evensidemargin
                                     \advance\@tempdima1in
                                     \advance\@tempdima\hoffset
                                     \hb@xt@\@tempdima{%
                                       \textcolor{darkgray}{\normalsize\sffamily
                                       \bfseries\quad
                                       \expandafter\textsolittle
                                       \expandafter{\@EventShortName}}%
                                     \strut\hss}}}}}
    \let\@evenfoot\@empty
    \let\@mkboth\markboth
  \let\sectionmark\@gobble
  \let\subsectionmark\@gobble}
\pagestyle{headings}
\renewcommand\maketitle{\par
  \begingroup
    \thispagestyle{plain}
    \renewcommand\thefootnote{\@fnsymbol\c@footnote}%
    \if@twocolumn
      \ifnum \col@number=\@ne
        \@maketitle
      \else
        \twocolumn[\@maketitle]%
      \fi
    \else
      \newpage
      \global\@topnum\z@   % Prevents figures from going at top of page.
      \@maketitle
    \fi
    \thispagestyle{plain}\@thanks
  \endgroup
  \global\let\thanks\relax
  \global\let\maketitle\relax
  \global\let\@maketitle\relax
  \global\let\@thanks\@empty
  \global\let\@author\@empty
  \global\let\@date\@empty
  \global\let\@title\@empty
  \global\let\title\relax
  \global\let\author\relax
  \global\let\date\relax
  \global\let\and\relax
}
\newwrite\tocfile
\def\@maketitle{%
  \newpage
  \null\vskip-\baselineskip
  \vskip-\headsep
  \@titlerunning
  \@authorrunning
  %%\let \footnote \thanks
  \parindent\z@ \raggedright
  \if!\@title!\def\@title{\textcolor{red}{Author: Please fill in a title}}\fi
    {\LARGE\sffamily\bfseries\mathversion{bold}\@title \par}%
    \vskip 1em
    \ifx\@author\orig@author
      \textcolor{red}{Author: Please provide author information}%
    \else
      {\def\thefootnote{\@arabic\c@footnote}%
       \setcounter{footnote}{0}%
       \fontsize{9.5}{12}\selectfont\@author}%
    \fi
    \bgroup
      \immediate\openout\tocfile=\jobname.vtc
      \protected@write\tocfile{
			\let\footnote\@gobble
			\let\thanks\@gobble
			\def\footnotemark{}
			\def\and{and }%
			\def\,{ }
			\def\\{ }
		}{%
	        \string\contitem
	        \string\title{\@title}%
	        \string\author{\@authorsfortoc}%
	        \string\page{\@Article:\thepage--\@Article:\number\numexpr\getpagerefnumber{TotPages}}}%
      \closeout\tocfile
    \egroup
  \par}
\renewcommand\tableofcontents{%
  \ifLineNumbers\nolinenumbers\let\linno@n\relax\fi
  \section*{\contentsname}%
  \@starttoc{toc}%
  \ifx\linno@n\relax\linenumbers\fi}
\setcounter{secnumdepth}{4}
\renewcommand\section{\@startsection {section}{1}{\z@}%
                                   {-3.5ex \@plus -1ex \@minus -.2ex}%
                                   {2.3ex \@plus.2ex}%
                                   {\sffamily\Large\bfseries\raggedright}}
\renewcommand\subsection{\@startsection{subsection}{2}{\z@}%
                                     {-3.25ex\@plus -1ex \@minus -.2ex}%
                                     {1.5ex \@plus .2ex}%
                                     {\sffamily\Large\bfseries\raggedright}}
\renewcommand\subsubsection{\@startsection{subsubsection}{3}{\z@}%
                                     {-3.25ex\@plus -1ex \@minus -.2ex}%
                                     {1.5ex \@plus .2ex}%
                                     {\sffamily\Large\bfseries\raggedright}}
\renewcommand\paragraph{\@startsection{paragraph}{4}{\z@}%
                                    {-3.25ex \@plus-1ex \@minus-.2ex}%
                                    {1.5ex \@plus .2ex}%
                                    {\sffamily\large\bfseries\raggedright}}
\renewcommand\subparagraph{\@startsection{subparagraph}{5}{\z@}%
                                       {3.25ex \@plus1ex \@minus .2ex}%
                                       {-1em}%
                                      {\sffamily\normalsize\bfseries}}
\setlength\leftmargini  \parindent
\setlength\leftmarginii {1.2em}
\setlength\leftmarginiii{1.2em}
\setlength\leftmarginiv {1.2em}
\setlength\leftmarginv  {1.2em}
\setlength\leftmarginvi {1.2em}
\renewcommand\labelenumi{%
  \textcolor{dartsGray}{\sffamily\bfseries\upshape\mathversion{bold}\theenumi.}}
\renewcommand\labelenumii{%
  \textcolor{dartsGray}{\sffamily\bfseries\upshape\mathversion{bold}\theenumii.}}
\renewcommand\labelenumiii{%
  \textcolor{dartsGray}{\sffamily\bfseries\upshape\mathversion{bold}\theenumiii.}}
\renewcommand\labelenumiv{%
  \textcolor{dartsGray}{\sffamily\bfseries\upshape\mathversion{bold}\theenumiv.}}
\renewcommand\labelitemi{%
  \textcolor{dartsBulletGray}{\ifnum\@listdepth=\@ne
                                  \rule{0.67em}{0.33em}%
                                \else
                                  \rule{0.45em}{0.225em}%
                                \fi}}
\renewcommand\labelitemii{%
  \textcolor{dartsBulletGray}{\rule{0.45em}{0.225em}}}
\renewcommand\labelitemiii{%
  \textcolor{dartsBulletGray}{\sffamily\bfseries\textasteriskcentered}}
\renewcommand\labelitemiv{%
  \textcolor{dartsBulletGray}{\sffamily\bfseries\textperiodcentered}}
\renewenvironment{description}
               {\list{}{\advance\partopsep\topsep\topsep\z@\@plus\p@
                        \labelwidth\z@ \itemindent-\leftmargin
                        \let\makelabel\descriptionlabel}}
               {\ifnum\@listdepth=\@ne\global\@nobotseplisttrue\fi\endlist}
\renewcommand*\descriptionlabel[1]{%
  \hspace\labelsep\textcolor{dartsGray}{\sffamily\bfseries\mathversion{bold}#1}}
\def\topmattervskip{0.2}
\newsavebox{\metadatabox}
\newenvironment{colbox}
  {\begin{lrbox}{\metadatabox}%
   \begin{minipage}{\dimexpr\columnwidth-2\fboxsep\relax}}
  {\end{minipage}\end{lrbox}%
   \begin{center}
   \colorbox[rgb]{0.85,0.85,0.86}{\usebox{\metadatabox}}
   \end{center}}
\renewenvironment{abstract}
  {\vskip\bigskipamount
   \ifLineNumbers\nolinenumbers\let\linno@n\relax\fi
   \multicolsep\z@
   \columnsep\parindent
   \begin{multicols}{2}%
     [\noindent
      \rlap{\color[rgb]{0.51,0.50,0.52}\vrule\@width\textwidth\@height1\p@}%
      {\hspace*{4.5mm}\fboxsep1.5mm\colorbox[rgb]{1,1,1}{\raisebox{-0.4ex}{%
       \large\selectfont\sffamily\bfseries\abstractname}}}%
      \vskip3\p@]%
   \fontsize{9}{12}\selectfont
   \noindent\ignorespaces}
  {\end{multicols}%
   \vskip0.5\baselineskip\noindent
   \begin{colbox}
     \fontsize{9}{12}\selectfont
     \vskip\topmattervskip\baselineskip\noindent
     \subjclassHeading
     \ifx\@ccsdescString\@empty
     	\textcolor{red}{Author: Please fill in 1 or more \string\ccsdesc\space macro}%
     \else
     	\@ccsdescString
   	 \fi
     \vskip\topmattervskip\baselineskip\noindent
     \keywordsHeading
     \ifx\@keywords\@empty
      \textcolor{red}{MANDATORY: Please provide 1--5 keywords as a comma-separated list}
     \else
      \@keywords
     \fi
	 \ifx\@DOIPrefix\@empty\else
     	\vskip\topmattervskip\baselineskip\noindent
     	\doiHeading
     	\ifx\@Volume\@empty
     		\textcolor{blue}{\@DOIPrefix.VOL.ISS.ART}
     	\else
     		\ifx\@Issue\@empty
     			\textcolor{blue}{\@DOIPrefix.VOL.ISS.ART}
     		\else
     			\ifx\@Article\@empty
     				\textcolor{blue}{\@DOIPrefix.VOL.ISS.ART}
     			\else
     				\href{https://doi.org/\@DOIPrefix.\@Volume.\@Issue.\@Article}{\@DOIPrefix.\@Volume.\@Issue.\@Article}
     			\fi
     		\fi
     	\fi 		
     \fi
	 \ifx\@funding\@empty\else
     \vskip\topmattervskip\baselineskip\noindent
     \fundingHeading\@funding
   \fi
   \ifx\@acknowledgements\@empty\else
     \vskip\topmattervskip\baselineskip\noindent
     \acknowledgementsHeading\ifx\authoranonymous\relax\textcolor{red}{Anonymous acknowledgements}\else\@acknowledgements\fi%
   \fi

     \vskip\topmattervskip\baselineskip\vskip\topmattervskip\baselineskip\noindent
     \ifx\@RelatedArticle\@empty\else
      \vskip\topmattervskip\baselineskip\noindent
      \RelatedArticleHeading\ifx\authoranonymous\relax\textcolor{red}{Anonymous related article}\else\@RelatedArticle\fi%
     \fi
     \ifx\@RelatedConference\@empty\else
      \vskip\topmattervskip\baselineskip\noindent
      \RelatedConferenceHeading\@RelatedConference
     \fi
      \vskip0.3\baselineskip\noindent
     \par
   \end{colbox}
   \ifx\linno@n\relax\linenumbers\fi}
\renewenvironment{thebibliography}[1]
  {\if@noskipsec \leavevmode \fi
   \par
   \ifLineNumbers\nolinenumbers\let\linno@n\relax\fi
   \@tempskipa-3.5ex \@plus -1ex \@minus -.2ex\relax
   \@afterindenttrue
   \@tempskipa -\@tempskipa \@afterindentfalse
   \if@nobreak
     \everypar{}%
   \else
     \addpenalty\@secpenalty\addvspace\@tempskipa
   \fi
   \columnsep\parindent
   \begin{multicols}{2}%
     [\noindent
      \rlap{\color[rgb]{0.51,0.50,0.52}\vrule\@width\textwidth\@height1\p@}%
      {\hspace*{4.5mm}\fboxsep1.5mm\colorbox[rgb]{1,1,1}{\raisebox{-0.4ex}{%
      \normalsize\sffamily\bfseries\refname}}}%
      \@xsect{1ex \@plus.2ex}%
     \vspace{-\multicolsep}]%
     \list{\@biblabel{\@arabic\c@enumiv}}%
        {\leftmargin6mm
         \labelsep\leftmargin
         \settowidth\labelwidth{\@biblabel{#1}}%
         \advance\labelsep-\labelwidth
         \usecounter{enumiv}%
         \let\p@enumiv\@empty
         \renewcommand\theenumiv{\@arabic\c@enumiv}}%
     \fontsize{8}{9.5}\selectfont
     \sloppy
     \clubpenalty10000
     \@clubpenalty \clubpenalty
     \widowpenalty10000%
     \sfcode`\.\@m}
  {\def\@noitemerr
       {\@latex@warning{Empty `thebibliography' environment}}%
     \endlist
   \end{multicols}%
   \ifx\linno@n\relax\linenumbers\fi}
\renewcommand\footnoterule{%
  \kern-8\p@
  {\color[rgb]{0.60,0.60,0.61}\hrule\@width40mm\@height1\p@}%
  \kern6.6\p@}
\renewcommand\@makefntext[1]{%
    \parindent\z@\hangindent1em
    \leavevmode
    \hb@xt@1em{\@makefnmark\hss}#1}
\newcommand\flag[2][0.9cm]{%
    \leavevmode\marginpar{%
        \raisebox{\dimexpr-\totalheight+\ht\strutbox\relax}%
        [\dimexpr\ht\strutbox+3mm][\dp\strutbox]{\expandafter\includegraphics[width=#1]{#2}}%
}}
\def\funding#1{\def\@funding{#1}}
\let\@funding\@empty
\def\fundingHeading{%
 \textcolor{darkgray}{\fontsize{9}{12}\sffamily\bfseries
                      Funding\enskip}}
\def\acknowledgements#1{\def\@acknowledgements{#1}}
\let\@acknowledgements\@empty
\def\acknowledgementsHeading{%
 \textcolor{darkgray}{\fontsize{9}{12}\sffamily\bfseries
                      Acknowledgements\enskip}}
\usepackage{microtype}
\usepackage[utf8]{inputenc}
\IfFileExists{glyphtounicode.tex}{
\input glyphtounicode
\pdfgentounicode=1
}{}%
\IfFileExists{lmodern.sty}{\RequirePackage{lmodern}}{}
\IfFileExists{fontawesome5.sty}{%
\RequirePackage{fontawesome5}%
\IfFileExists{orcid.pdf}{%
\def\orcidsymbol{\includegraphics[height=9\p@]{orcid}}
}{
\def\orcidsymbol{\textcolor{dartsGray}{\fontsize{9}{12}\sffamily\bfseries \faOrcid}}%
}
\def\mailsymbol{\textcolor{dartsGray}{\fontsize{9}{12}\sffamily\bfseries \faIcon[regular]{envelope}}}%
\def\homesymbol{\textcolor{dartsGray}{\fontsize{9}{12}\sffamily\bfseries \faHome}}%
}{%
\ClassWarning{Package fontawesome5 not installed}{Please install package fontawesome5}
\def\orcidsymbol{\textcolor{dartsGray}{\fontsize{9}{12}\sffamily\bfseries ORCID}}
\def\mailsymbol{\textcolor{dartsGray}{\fontsize{9}{12}\sffamily\bfseries @}}%
\def\homesymbol{\textcolor{dartsGray}{\fontsize{9}{12}\sffamily\bfseries H}}%
}%
\RequirePackage[T1]{fontenc}
\RequirePackage{textcomp}
\RequirePackage[mathscr]{eucal}
\RequirePackage{amssymb}
\RequirePackage{soul}
\sodef\textsolittle{}{.12em}{.5em\@plus.08em\@minus.06em}%
        {.4em\@plus.275em\@minus.183em}
\RequirePackage{color} %kept for backward compatibility
\AtBeginDocument{
	\@ifpackageloaded{xcolor}{
	}{
		\RequirePackage{xcolor}
	}
	\definecolor{darkgray}{rgb}{0.31,0.31,0.33}
	\definecolor[named]{dartsGray}{rgb}{0.31,0.31,0.33}
	\definecolor[named]{dartsBulletGray}{rgb}{0.60,0.60,0.61}
	\definecolor[named]{dartsLineGray}{rgb}{0.51,0.50,0.52}
	\definecolor[named]{dartsLightGray}{rgb}{0.85,0.85,0.86}
	\definecolor[named]{dartsYellow}{rgb}{0.99,0.78,0.07}
}
\RequirePackage{babel}
\RequirePackage[tbtags,fleqn]{amsmath}
\RequirePackage{amsthm}
\thm@headfont{%
  \textcolor{darkgray}{$\blacktriangleright$}\nobreakspace\sffamily\bfseries}
\def\th@remark{%
  \thm@headfont{%
    \textcolor{darkgray}{$\blacktriangleright$}\nobreakspace\sffamily}%
  \normalfont % body font
  \thm@preskip\topsep \divide\thm@preskip\tw@
  \thm@postskip\thm@preskip
}
\def\@endtheorem{\endtrivlist}%\@endpefalse
\renewcommand\qedsymbol{\textcolor{darkgray}{\ensuremath{\blacktriangleleft}}}
\renewenvironment{proof}[1][\proofname]{\par
  \pushQED{\qed}%
  \normalfont \topsep6\p@\@plus6\p@\relax
  \trivlist
  \item[\hskip\labelsep
        \color{darkgray}\sffamily\bfseries
    #1\@addpunct{.}]\ignorespaces
}{%
  \popQED\endtrivlist%\@endpefalse
}
\theoremstyle{plain}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{example}[theorem]{Example}
\theoremstyle{remark}
\newtheorem*{remark}{Remark}
\ifx\numberwithinsect\relax
  \@addtoreset{theorem}{section}
  \edef\thetheorem{\expandafter\noexpand\thesection\@thmcountersep\@thmcounter{theorem}}
\fi
\RequirePackage{graphicx}
\RequirePackage{array}
\let\@classzold\@classz
\def\@classz{%
   \expandafter\ifx\d@llarbegin\begingroup
     \toks \count@ =
     \expandafter{\expandafter\small\the\toks\count@}%
   \fi
   \@classzold}
\RequirePackage{multirow}
\RequirePackage{tabularx}
\RequirePackage[online]{threeparttable}
\def\TPTtagStyle#1{#1)}
\def\tablenotes{\small\TPT@defaults
  \@ifnextchar[\TPT@setuptnotes\TPTdoTablenotes} % ]
\RequirePackage{listings}
\lstset{basicstyle=\small\ttfamily,%
        backgroundcolor=\color{dartsLightGray},%
        frame=single,framerule=0pt,xleftmargin=\fboxsep,xrightmargin=\fboxsep}
\RequirePackage{multicol}[2011/06/27]
\multicolsep = 13pt plus 4pt minus 3pt
\RequirePackage[left,mathlines]{lineno}
\linenumbers
\renewcommand\linenumberfont{\normalfont\tiny\sffamily}
%%%% patch to cope with amsmath
%%%% http://phaseportrait.blogspot.de/2007/08/lineno-and-amsmath-compatibility.html
\newcommand*\patchAmsMathEnvironmentForLineno[1]{%
  \expandafter\let\csname old#1\expandafter\endcsname\csname #1\endcsname
  \expandafter\let\csname oldend#1\expandafter\endcsname\csname end#1\endcsname
  \renewenvironment{#1}%
     {\linenomath\csname old#1\endcsname}%
     {\csname oldend#1\endcsname\endlinenomath}}%
\newcommand*\patchBothAmsMathEnvironmentsForLineno[1]{%
  \patchAmsMathEnvironmentForLineno{#1}%
  \patchAmsMathEnvironmentForLineno{#1*}}%
\AtBeginDocument{%
  \patchBothAmsMathEnvironmentsForLineno{equation}%
  \patchBothAmsMathEnvironmentsForLineno{align}%
  \patchBothAmsMathEnvironmentsForLineno{flalign}%
  \patchBothAmsMathEnvironmentsForLineno{alignat}%
  \patchBothAmsMathEnvironmentsForLineno{gather}%
  \patchBothAmsMathEnvironmentsForLineno{multline}}
\let\usehyperxmp\@empty%
\ifx\pdfa\relax%
  \IfFileExists{hyperxmp.sty}{%
    \RequirePackage{hyperxmp}%
    \@ifpackagelater{hyperxmp}{2019/04/05}{%
      \let\usehyperxmp\relax%
    }{%
      \ClassWarning{Package hyperxmp outdated}{You are using an outdated version of the package hyperxmp. Please update!}%
    }}{}%
\fi%
\IfFileExists{totpages.sty}{
  \RequirePackage{totpages}
}{
	\ClassWarning{Package totpages not installed}{Please install package totpages}
	\newcounter{TotPages}
	\setcounter{TotPages}{99}
}
\ifx\usehyperxmp\relax%
  \RequirePackage[pdfa,unicode]{hyperref}%
\else%
  \RequirePackage[unicode]{hyperref}%
\fi%
\let\C\relax%
\let\G\relax%
\let\F\relax%
\let\U\relax%
\pdfstringdefDisableCommands{%
	\let\thanks\@gobble%
	\let\footnote\@gobble%
	\def\footnotemark{}%
	\def\cs#1{\textbackslash #1}%
	\let\normalfont\@empty%
	\let\scshape\@empty%
	\def\and{and }%
	\def\,{ }%
	\def\textrightarrow{ -> }%
	\let\mathsf\@empty%
}%
\hypersetup{
	breaklinks=true,
	pdfencoding=unicode,
	bookmarksnumbered,
	pdfborder={0 0 0},
	pdfauthor={ }
}%
\AtBeginDocument{
\ifx\usehyperxmp\relax
\hypersetup{
pdftitle={\@title},
pdfauthor={\ifx\authoranonymous\relax Anonymous author(s) \else\@authorsforpdf\fi},
pdfkeywords={\@keywords},
pdfproducer={LaTeX with darts-v2021.cls},
pdfsubject={DARTS, Vol. \@Volume, Issue \@Issue, Article \@Article},
pdfcopyright = { Copyright (C) \ifx\authoranonymous\relax Anonymous author(s) \else \@copyrightholder; \fi licensed under Creative Commons License CC-BY 4.0},
pdflang={en},
pdfmetalang={en},
pdfpublisher={Schloss Dagstuhl -- Leibniz-Zentrum für Informatik, Dagstuhl Publishing, Germany},
pdflicenseurl={https://creativecommons.org/licenses/by/4.0/},
pdfpubtype={DARTS},
pdfvolumenum={\@Volume},
pdfpagerange={\@Article:\thepage-\@Article:\theTotPages},
pdfdoi={\@DOIPrefix.\@Volume.\@Issue.\@Article},
pdfapart=3,
pdfaconformance=B
}
\else%
\hypersetup{
pdftitle={\@title},
pdfauthor={\ifx\authoranonymous\relax Anonymous author(s) \else\@authorsforpdf\fi},
pdfkeywords={\@keywords},
pdfcreator={LaTeX with darts-v2021.cls},
pdfsubject={DARTS, Vol. \@Volume, Issue \@Issue, Article \@Article; Copyright (C) \ifx\authoranonymous\relax Anonymous author(s) \else \@copyrightholder; \fi licensed under Creative Commons License CC-BY 4.0}
}%
\fi	%
}
\ifx\usehyperxmp\relax
\pdfobjcompresslevel=0
\pdfinclusioncopyfonts=1
\IfFileExists{colorprofiles.tex}{
\RequirePackage{colorprofiles}%
\IfFileExists{sRGB.icc}{
\immediate\pdfobj stream attr{/N 3} file{sRGB.icc}
\pdfcatalog{%
/OutputIntents [
<<
/Type /OutputIntent
/S /GTS_PDFA1
/DestOutputProfile \the\pdflastobj\space 0 R
/OutputConditionIdentifier (sRGB)
/Info (sRGB)
>>
]
}}{}
}{\ClassWarning{Package colorprofiles not installed}{Please install package colorprofiles}}
\fi
\RequirePackage[labelsep=space,singlelinecheck=false,%
  font={up,small},labelfont={sf,bf},%
  listof=false]{caption}%"listof" instead of "list" for backward compatibility
\@ifpackagelater{hyperref}{2009/12/09}
  {\captionsetup{compatibility=false}}%cf. http://groups.google.de/group/comp.text.tex/browse_thread/thread/db9310eb540fbbd8/42e30f3b7b3aa17a?lnk=raot
  {}
\DeclareCaptionLabelFormat{boxed}{%
  \kern0.05em{\color[rgb]{0.99,0.78,0.07}\rule{0.73em}{0.73em}}%
  \hspace*{0.67em}\bothIfFirst{#1}{~}#2}
\captionsetup{labelformat=boxed}
\captionsetup[table]{position=top}
\RequirePackage[figuresright]{rotating}
\caption@AtBeginDocument{\@ifpackageloaded{subfig}{\ClassError{darts}{%
  Do not load the subfig package}{The more recent subcaption package is already loaded}}{}}
\RequirePackage{subcaption}
\def\titlerunning#1{\gdef\@titlerunning{{\let\footnote\@gobble\markboth{#1}{#1}}}}
\def\authorrunning#1{%
  \gdef\@authorrunning{\markright{\ifx\authoranonymous\relax\textcolor{red}{Anonymous author(s)} \else\if!#1!\textcolor{red}{Author: Please fill in the \string\authorrunning\space macro}\else#1\fi\fi}}}
\titlerunning{\@title}
\authorrunning{\textcolor{red}{Author: Please use the \string\authorrunning\space macro}}
\def\Volume#1{\gdef\@Volume{#1}}
\Volume{}
\def\Issue#1{\gdef\@Issue{#1}}
\Issue{}
\def\Article#1{\gdef\@Article{#1}}
\Article{}
\def\FirstPage#1{\setcounter{page}{#1}}
\def\DOIPrefix#1{\gdef\@DOIPrefix{#1}}
\DOIPrefix{10.4230/DARTS}
\def\and{\newline}
\let\orig@author\@author
\let\@authorsfortoc\@empty
\let\@authorsforpdf\@empty
\newcount\c@author
\newcounter{currentauthor}
\def\authorcolumnsMin{6}
\def\@authornum{0}
\def\author#1#2#3#4#5{%
  \ifx\@author\orig@author\let\@author\@empty\fi
  \g@addto@macro\@author{%
	\noexpandarg\StrBehind{#2}{\and \url}[\homepageTemp]\IfSubStr{#2}{\and \url}{\StrBefore{#2}{\and \url}[\affiliation]}{\def\affiliation{#2}}%
	\expandarg\exploregroups\StrRemoveBraces{\homepageTemp}[\homepage]%
	\ifx\authorcolumns\relax
		\ifnum\c@author>\authorcolumnsMin
			\stepcounter{currentauthor}
			\ifodd\value{currentauthor}
				\begin{minipage}[t]{\textwidth}
				\begin{minipage}[t]{0.49\textwidth}
			\else
				\hfill \begin{minipage}[t]{0.49\textwidth}
			\fi
		\else
			\ClassWarning{Option 'authorcolumns' only applicable for > 6 authors}{Option 'authorcolumns' only applicable for >6 authors!}
			\addvspace{0.5\baselineskip}
		\fi
	\else
		\addvspace{0.5\baselineskip}
	\fi
    {\Large\bfseries
     \if!#1!
       \textcolor{red}{Author: Please enter author name}%
     \else
       \ifx\authoranonymous\relax
			\textcolor{red}{Anonymous author}
		\else
			#1\,%
			\ifx\compactauthor\relax\if!#3!\else{\,\href{mailto:#3}{\mailsymbol}}\fi%
			\ifx\homepage\@empty\else{\,\href{\homepage}{\homesymbol}}\fi\fi%
			\if!#4!\else{\,\href{#4}{\orcidsymbol}}\fi%
			\if!#5!\else
				\ifx\@funding\@empty
					\expandafter\g@addto@macro\expandafter\@funding{\textit{\expandafter{\let\footnote\@gobble #1}}:\space{#5}}
				\else
					\expandafter\g@addto@macro\expandafter\@funding{\\\textit{\expandafter{\let\footnote\@gobble #1}}:\space{#5}}
				\fi
			\fi
		\fi
     \fi
     }
	{\small
    \if!#2!\textcolor{red}{Author: Please enter affiliation as second parameter of the author macro}\else{\\* \ifx\authoranonymous\relax\textcolor{red}{Anonymous affiliation}\else\ifx\compactauthor\relax \affiliation \else#2\fi\fi}\fi
    \ifx\compactauthor\relax\else\if!#3!\else{\ifx\authoranonymous\relax\else\\*\href{mailto:#3}{#3}\fi}\fi\fi
	}\par
	\ifx\authorcolumns\relax
		\ifnum\c@author>\authorcolumnsMin
			\end{minipage}
			\ifnum\c@author=\value{currentauthor}
				\end{minipage}
			\else
				\ifodd\value{currentauthor}
				\else
					\end{minipage}%
					\medskip
				\fi
			\fi
		\fi
	\fi}%
  \global\advance\c@author\@ne
  \protected@write\@auxout{}{\string\gdef\string\@authornum{\the\c@author}}
  \ifnum\c@author=\@ne
    \gdef\@authorsfortoc{#1}%
    \gdef\@authorsforpdf{#1}
  \else
    \expandafter\g@addto@macro\expandafter\@authorsforpdf\expandafter{, #1}
    \expandafter\g@addto@macro\expandafter\@authorsfortoc\expandafter{\expandafter\csname\the\c@author authand\endcsname#1}%
    \@namedef{\the\c@author authand}{,\space}%
    \AtBeginDocument{%
      \expandafter\ifnum\@authornum=2
        \@namedef{2authand}{\space and\space}%
      \else
        \@namedef{\@authornum authand}{,\space and\space}%
      \fi}
  \fi}
\newcommand*\affil[2][]{%
  \ClassError{darts}
    {\string\affil\space deprecated: Please enter affiliation as second parameter of the author macro}
    {Since 2017, \string\affil\space is obsolete in darts.}}
\newcommand*\Copyright[1]{%
  \def\@copyrightholder{#1}
  \def\@Copyright{%
    \setbox\@tempboxa\hbox{\includegraphics[height=14\p@,clip]{cc-by}}%
    \@rightskip\@flushglue \rightskip\@rightskip
    \hangindent\dimexpr\wd\@tempboxa+0.5em\relax
    \href{https://creativecommons.org/licenses/by/4.0/}%
         {\smash{\lower\baselineskip\hbox{\unhcopy\@tempboxa}}}\enskip
    \textcopyright\ %
    \ifx!#1!\textcolor{red}{Author: Please fill in the \string\Copyright\space macro}\else\ifx\authoranonymous\relax\textcolor{red}{Anonymous author(s)}\else#1\fi\fi
    ;\\%
    licensed under Creative Commons License CC-BY 4.0\ifx!#1!\\\null\fi\par}}
\Copyright{\textcolor{red}{Author: Please provide a copyright holder}}
\let\@copyrightholder\@empty
\def\keywords#1{\def\@keywords{#1}}
\let\@keywords\@empty
\def\keywordsHeading{%
  \textcolor{darkgray}{\fontsize{9}{12}\sffamily\bfseries
                       Keywords and phrases\enskip}}
\RequirePackage{comment}
\excludecomment{CCSXML}
% inspired by https://tex.stackexchange.com/questions/12810/how-do-i-split-a-string
\global\newcommand\ccsdesc[2][100]{\@ccsdesc#1~#2~~\relax}
\usepackage{xstring}
\let\orig@ccsdesc\@ccsdesc
\let\@ccsdesc\@empty
\let\@ccsdescString\@empty
\gdef\@ccsdesc#1~#2~#3~{
	\ifx\@ccsdesc\orig@ccsdesc\let\@ccsdesc\@empty\fi
	\ifx!#3!
		\ifx\@ccsdescString\@empty
			\g@addto@macro\@ccsdescString{{#2}}
		\else
			\g@addto@macro\@ccsdescString{; {#2}}
		\fi
	\else
		\ifx\@ccsdescString\@empty
			\g@addto@macro\@ccsdescString{{#2} $\rightarrow$ {#3}}
		\else
			\g@addto@macro\@ccsdescString{; {#2} $\rightarrow$ {#3}}
		\fi
	\fi
\ccsdescEnd
}
\def\ccsdescEnd#1\relax{}
\def\subjclass#1{
  \ClassError{darts}
    {\string\subjclass\space deprecated: Please enter subject classification in 1 or more ccsdesc macros}
    {Since 2019, \string\subjclass\space is obsolete in darts.}}
\let\@subjclass\@empty
\def\subjclassHeading{%
  \textcolor{darkgray}{\fontsize{9}{12}\sffamily\bfseries
                       2012 ACM Subject Classification\enskip}}
\def\doiHeading{%
  \textcolor{darkgray}{\fontsize{9}{12}\sffamily\bfseries
                       Digital Object Identifier\enskip}}
\def\RelatedConference#1{\gdef\@RelatedConference{#1}}
\def\RelatedConferenceHeading{%
  \textcolor{darkgray}{\fontsize{9}{12}\sffamily\bfseries
                      Related Conference\enskip}}
\let\@RelatedConference\@empty
\def\RelatedArticle#1{\gdef\@RelatedArticle{#1}}
\def\RelatedArticleHeading{%
  \textcolor{darkgray}{\fontsize{9}{12}\sffamily\bfseries
                      Related Article\enskip}}
\let\@RelatedArticle\@empty
\def\EventShortName#1{\gdef\@EventShortName{#1}}
\EventShortName{DARTS}
\endinput
%%
%% End of file `darts.cls'.
