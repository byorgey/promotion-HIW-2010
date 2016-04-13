%% -*- LaTeX -*-
\documentclass[xcolor=svgnames,12pt]{beamer}

%include polycode.fmt

\mode<presentation>
{
  \usetheme{default}                          % use a default (plain) theme

  \setbeamertemplate{navigation symbols}{}    % don't show navigation
                                              % buttons along the
                                              % bottom
  \setbeamerfont{normal text}{family=\sffamily}

  \setbeamertemplate{footline}[frame number]

  \AtBeginSection[]
  {
    \begin{frame}<beamer>
      \frametitle{Outline}
      \tableofcontents[currentsection,currentsubsection]
    \end{frame}
  }
}

% \setbeameroption{show only notes}

\usepackage[english]{babel}
\usepackage{graphicx}
\usepackage{ulem}
\usepackage{url}
\usepackage{fancyvrb}

\usepackage{brent}

\newcommand{\tk}{\tau\!\!\!\kappa}
\newcommand{\altc}{\;||\;}

\graphicspath{{images/}}

\title{Typed type-level functional programming with GHC}
\date{Haskell Implementors' Workshop \\ October 1, 2010}
\author{Brent Yorgey \\ University of Pennsylvania}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

  \begin{frame}{}
    \titlepage
   \includegraphics[width=0.8in]{images/haskell-logo.pdf}
   \hfill
   \includegraphics[width=0.5in]{images/plclub.png}
  \end{frame}

  \title{What I Did On My Summer Vacation}

  \begin{frame}
    \titlepage
   \includegraphics[width=0.8in]{images/haskell-logo.pdf}
   \hfill
   \includegraphics[width=0.5in]{images/plclub.png}
  \end{frame}

  \title{What I Did On My Summer \sout{Vacation} Holiday}

  \begin{frame}
    \titlepage
   \includegraphics[width=0.8in]{images/haskell-logo.pdf}
   \hfill
   \includegraphics[width=0.5in]{images/plclub.png}
  \end{frame}

  \begin{frame}
    Joint work-in-progress with: 

    \begin{center}
      \parbox{2in}{
        \begin{center}
          \includegraphics[width=0.5in]{images/spj.jpg} \\
          Simon Peyton-Jones
        \end{center}
      }
      \parbox{2in}{
        \begin{center}
          \includegraphics[width=0.5in]{images/dimitrios.jpg} \\
          Dimitrios Vytiniotis
        \end{center}
      } \\

      \parbox{2in}{
        \begin{center}
          \includegraphics[width=0.5in]{images/stephanie.jpg} \\
          Stephanie Weirich
        \end{center}
      }
      \parbox{2in}{
        \begin{center}
          \includegraphics[width=0.5in]{images/steve.jpg} \\
          Steve Zdancewic
        \end{center}
      }
      
    \end{center}
  \end{frame}

%   \begin{frame}
%     \begin{verbatim}
% {-# LANGUAGE EmptyDataDecls,
%              TypeFamilies,
%              GADTs,
%              ???                #-}
%     \end{verbatim}
%   \end{frame}

\section{Type-level programming}

  \begin{frame}{Type-level naturals}
    \begin{code}
data Z
data S n

type family Plus (m::*) (n::*) :: *
type instance Plus Z     n = n
type instance Plus (S m) n = S (Plus m n)
    \end{code}
  \end{frame}

  \begin{frame}{Length-indexed vectors}
    \begin{code}
data Vec :: * -> * -> * where
  Nil  :: Vec Z a
  Cons :: a -> Vec n a -> Vec (S n) a    
    \end{code}

    \onslide<2>{
      \begin{code}
append :: Vec m a -> Vec n a -> Vec (Plus m n) a
append Nil         v = v
append (Cons x xs) v = Cons x (append xs v)       
      \end{code}
    }
  \end{frame}

  \begin{frame}{Problems}
    \onslide<1->
    \begin{code}
data Nat = Z | S Nat

data Z    -- duplicate!
data S n
    \end{code}

    \onslide<2->
    \begin{code}
data Vec :: * -> * -> *   -- untyped!
    \end{code}

    \onslide<3->
  \begin{code}
Vec Int (S Z)  -- ?
Vec (S Z) Int  -- ?
  \end{code}
  \end{frame}

  \begin{frame}{The goal}
    \begin{center}
    \only<1>{
      Taking inspiration from SHE\dots
    }
    \only<2>{
      Taking inspiration from \sout{SHE} HER\dots
    }
    \end{center}      
  \end{frame}

  \begin{frame}[fragile]{The goal}
\begin{semiverbatim}
\textcolor{blue}{data Nat = Z || S Nat}

type family Plus (\textcolor{blue}{m::Nat}) (\textcolor{blue}{n::Nat}) :: \textcolor{blue}{Nat}
type instance Plus Z     n = n
type instance Plus (S m) n = S (Plus m n)    
\end{semiverbatim}

\onslide<2->
\begin{semiverbatim}
data Vec :: \textcolor{blue}{Nat} -> * -> * where
  Nil  :: Vec Z a
  Cons :: a -> Vec n a -> Vec (S n) a

append :: ...
\end{semiverbatim}
\onslide<3->
\dots Look, ma, no braces!
\end{frame}

\section{Theory}

\begin{frame}{GHC core}
\parbox{2in}{
\begin{align*}
  e & ::= x \altc K \\
    & \altc \Lambda a:\kappa. e \altc e \, \tau \\
    & \altc \lambda x:\sigma. e \altc e_1 \, e_2 \\
    & \altc let  ... \altc case ... \\
    & \altc e \vartriangleright \gamma
\end{align*}
}
\only<2-4>{
\parbox{2in}{
\begin{align*}
  \tau & ::= a \altc T \uncover<4->{\textcolor{blue}{\altc K}} \\
       & \altc \tau_1 \, \tau_2 \altc F_n \, \overline{\tau}^n  \\
       & \altc \forall a : \kappa. \tau
\end{align*}
}
}
\only<5->{
\parbox{2in}{
\begin{align*}
  \tk & ::= a \altc T \altc K \altc \color{blue}{\star} \\
       & \altc \tk_1 \tk_2 \altc F_n \overline{\tk}^n  \\
       & \altc \forall a : \tk. \tk
\end{align*}  
}
}
\only<3-4>{
\begin{align*}
  \kappa & ::= \textcolor<4>{red}{\star \altc \kappa_1 \to \kappa_2}
\end{align*}
}
\only<6->{
  \[ \Gamma \vdash \star : \star \]
}
\only<7->{
  \dots Why not collapse everything?
}
\end{frame}

\begin{frame}{Collapse everything?}
  \begin{itemize}
  \item<+-> Phase distinction!
  \item<+-> No need for erasure analysis
  \item<+-> Incremental change
  \end{itemize}
\end{frame}

\begin{frame}{Kind polymorphism!}
  \[ \forall \kappa:\star. \forall a:\kappa. \dots \]
\end{frame}

\begin{frame}{Typechecking coercions}
  \only<1>{
    \[ \forall a:\kappa.\tau_1 \sim \forall a:\kappa.\tau_2 \]
  }
  \only<2->{
    \[ \forall a:\kappa_1.\tau_1 \sim \forall a:\kappa_2.\tau_2 \]
  }
  \begin{itemize}
  \item<3-> Nontrivial kind equalities only come from GADTs\dots
  \item<4-> No lifting GADTs! (For now.)
  \end{itemize}
\end{frame}

\section{Implementation}

\begin{frame}{Progress}
  \begin{itemize}
  \item<+-> Currently refactoring coercions as a separate type
  \item<+-> Fix newtype deriving bug!
  \item<+-> Implement auto-lifting of non-GADTs
  \end{itemize}
\end{frame}

\section{Future work}

\begin{frame}
  \begin{center}
  Allow lifting GADTs?    
  \end{center}
\end{frame}

\begin{frame}
  \begin{center}
  Closed type functions?    
  \end{center}

  \begin{code}
data Nat = Z | S Nat

type family Pred (n::Nat) :: Nat
type instance Pred Z     = Z
type instance Pred (S n) = n
  \end{code}
\end{frame}

\begin{frame}
  \begin{center}
    Closed type classes?
  \end{center}

  \begin{code}
class Foo (n::Nat) where
  ...

instance Foo Z where ...
instance Foo (S n) where ...    
  \end{code}
\end{frame}

\begin{frame}
  \begin{center}
    Proof search/induction?
  \end{center}

  \begin{code}
                  Plus n Z ~ n
  \end{code}

\end{frame}

\begin{frame}
  \begin{center}
    Lifting value-level \emph{functions} to the type level?
  \end{center}
  \begin{code}
plus :: Nat -> Nat -> Nat
plus Z     n = n
plus (S m) n = S (plus m n)

append :: Vec m a -> Vec n a -> Vec (plus m n) a
...    
  \end{code}
\end{frame}

\begin{frame}
  \begin{center}
    Coming soon to a GHC near you!
  \end{center}
\end{frame}

\end{document}

