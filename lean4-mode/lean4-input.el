;;;  -*- lexical-binding: t -*-
;;; lean4-input.el --- The Lean input method (based/copied from Agda)
;;;
;;; DISCLAIMER: This file is based on agda-input.el provided with the Agda language.
;;; We did minor modifications
;;
;;; Commentary:
;;
;;;; A highly customisable input method which can inherit from other
;; Quail input methods. By default the input method is geared towards
;; the input of mathematical and other symbols in Lean programs.
;;
;; Use M-x customize-group lean4-input to customise this input method.
;; Note that the functions defined under "Functions used to tweak
;; translation pairs" below can be used to tweak both the key
;; translations inherited from other input methods as well as the
;; ones added specifically for this one.
;;
;; Use lean4-input-show-translations to see all the characters which
;; can be typed using this input method (except for those
;; corresponding to ASCII characters).

;;; Code:

(require 'quail)
(require 'cl-lib)

;; Quail is quite stateful, so be careful when editing this code.  Note
;; that with-temp-buffer is used below whenever buffer-local state is
;; modified.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility functions

(defun lean4-input-concat-map (f xs)
  "Concat (map F XS)."
  (apply 'append (mapcar f xs)))

(defun lean4-input-to-string-list (s)
  "Convert a string S to a list of one-character strings, after
removing all space and newline characters."
  (lean4-input-concat-map
   (lambda (c) (if (member c (string-to-list " \n"))
              nil
            (list (string c))))
   (string-to-list s)))

(defun lean4-input-character-range (from to)
  "A string consisting of the characters from FROM to TO."
  (let (seq)
    (dotimes (i (1+ (- to from)))
      (setq seq (cons (+ from i) seq)))
    (concat (nreverse seq))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions used to tweak translation pairs

(defun lean4-input-compose (f g)
  "\x -> concatMap F (G x)"
  (lambda (x) (lean4-input-concat-map f (funcall g x))))

(defun lean4-input-or (f g)
  "\x -> F x ++ G x"
  (lambda (x) (append (funcall f x) (funcall g x))))

(defun lean4-input-nonempty ()
  "Only keep pairs with a non-empty first component."
  (lambda (x) (if (> (length (car x)) 0) (list x))))

(defun lean4-input-prepend (prefix)
  "Prepend PREFIX to all key sequences."
    (lambda (x) `((,(concat prefix (car x)) . ,(cdr x)))))

(defun lean4-input-prefix (prefix)
  "Only keep pairs whose key sequence starts with PREFIX."
  (lambda (x)
    (if (equal (substring (car x) 0 (length prefix)) prefix)
        (list x))))

(defun lean4-input-suffix (suffix)
  "Only keep pairs whose key sequence ends with SUFFIX."
  (lambda (x)
    (if (equal (substring (car x)
                          (- (length (car x)) (length suffix)))
               suffix)
        (list x))))

(defun lean4-input-drop (ss)
  "Drop pairs matching one of the given key sequences.
SS should be a list of strings."
  (lambda (x) (unless (member (car x) ss) (list x))))

(defun lean4-input-drop-beginning (n)
  "Drop N characters from the beginning of each key sequence."
  (lambda (x) `((,(substring (car x) n) . ,(cdr x)))))

(defun lean4-input-drop-end (n)
  "Drop N characters from the end of each key sequence."
  (lambda (x)
    `((,(substring (car x) 0 (- (length (car x)) n)) .
       ,(cdr x)))))

(defun lean4-input-drop-prefix (prefix)
  "Only keep pairs whose key sequence starts with PREFIX.
This prefix is dropped."
  (lean4-input-compose
   (lean4-input-drop-beginning (length prefix))
   (lean4-input-prefix prefix)))

(defun lean4-input-drop-suffix (suffix)
  "Only keep pairs whose key sequence ends with SUFFIX.
This suffix is dropped."
  (lean4-input-compose
   (lean4-input-drop-end (length suffix))
   (lean4-input-suffix suffix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Customization

;; The :set keyword is set to 'lean4-input-incorporate-changed-setting
;; so that the input method gets updated immediately when users
;; customize it. However, the setup functions cannot be run before all
;; variables have been defined. Hence the :initialize keyword is set to
;; 'custom-initialize-default to ensure that the setup is not performed
;; until lean4-input-setup is called at the end of this file.

(defgroup lean4-input nil
  "The Lean input method.
After tweaking these settings you may want to inspect the resulting
translations using `lean4-input-show-translations'."
  :group 'lean
  :group 'leim)

(defcustom lean4-input-tweak-all
  '(lean4-input-compose
    (lean4-input-prepend "\\")
    (lean4-input-nonempty))
  "An expression yielding a function which can be used to tweak
all translations before they are included in the input method.
The resulting function (if non-nil) is applied to every
\(KEY-SEQUENCE . TRANSLATION) pair and should return a list of such
pairs. (Note that the translations can be anything accepted by
`quail-defrule'.)

If you change this setting manually (without using the
customization buffer) you need to call `lean4-input-setup' in
order for the change to take effect."
  :group 'lean4-input
  :set 'lean4-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type 'sexp)

(defcustom lean4-input-inherit
  `(("TeX" . (lean4-input-compose
              (lean4-input-drop '("geq" "leq" "bullet" "qed" "par"))
              (lean4-input-or
               (lean4-input-drop-prefix "\\")
               (lean4-input-or
                (lean4-input-compose
                 (lean4-input-drop '("^o"))
                 (lean4-input-prefix "^"))
                (lean4-input-prefix "_")))))
    )
  "A list of Quail input methods whose translations should be
inherited by the Lean input method (with the exception of
translations corresponding to ASCII characters).

The list consists of pairs (qp . tweak), where qp is the name of
a Quail package, and tweak is an expression of the same kind as
`lean4-input-tweak-all' which is used to tweak the translation
pairs of the input method.

The inherited translation pairs are added last, after
`lean4-input-user-translations' and `lean4-input-translations'.

If you change this setting manually (without using the
customization buffer) you need to call `lean4-input-setup' in
order for the change to take effect."
  :group 'lean4-input
  :set 'lean4-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type '(repeat (cons (string :tag "Quail package")
                       (sexp :tag "Tweaking function"))))

(defcustom lean4-input-translations
  (let ((max-lisp-eval-depth 2800)) `(

  ;; Negation

  ("not" . ("¬"))

  ;; Equality and similar symbols.

  ("eq"  . ,(lean4-input-to-string-list "=∼∽≈≋∻∾∿≀≃⋍≂≅ ≌≊≡≣≐≑≒≓≔≕≖≗≘≙≚≛≜≝≞≟≍≎≏≬⋕"))
  ("eqn" . ,(lean4-input-to-string-list "≠≁ ≉     ≄  ≇≆  ≢                 ≭    "))
  ("equiv" . ,(lean4-input-to-string-list "≃⋍"))
  ("iso" . ,(lean4-input-to-string-list "≅≌"))

                    ("=n"  . ("≠"))
  ("~"    . ("∼"))  ("~n"  . ("≁")) ("homotopy"    . ("∼"))
  ("~~"   . ("≈"))  ("~~n" . ("≉"))
  ("~~~"  . ("≋"))
  (":~"   . ("∻"))
  ("~-"   . ("≃"))  ("~-n" . ("≄"))
  ("-~"   . ("≂"))
  ("~="   . ("≅"))  ("~=n" . ("≇"))
  ("~~-"  . ("≊"))
  ("=="   . ("≡"))  ("==n" . ("≢"))
  ("==="  . ("≣"))
  (".="   . ("≐"))  (".=." . ("≑"))
  (":="   . ("≔"))  ("=:"  . ("≕"))
  ("=o"   . ("≗"))
  ("(="   . ("≘"))
  ("and=" . ("≙"))  ("or=" . ("≚"))
  ("*="   . ("≛"))
  ("t="   . ("≜"))
  ("def=" . ("≝"))
  ("m="   . ("≞"))
  ("?="   . ("≟"))

  ("pr" . ("↣"))

  ("1" . ("₁"))
  ("2" . ("₂"))
  ("3" . ("₃"))
  ("4" . ("₄"))
  ("5" . ("₅"))
  ("6" . ("₆"))
  ("7" . ("₇"))
  ("8" . ("₈"))
  ("9" . ("₉"))
  ("0" . ("₀"))

  ;; Inequality and similar symbols.

  ("leq"  . ,(lean4-input-to-string-list "≤≦≲<≪⋘ ≶≺≼≾⊂⊆ ⋐⊏⊑ ⊰⊲⊴⋖⋚⋜⋞"))
  ("leqn" . ,(lean4-input-to-string-list "≰≨≮≴⋦   ≸⊀ ⋨⊄⊈⊊  ⋢⋤ ⋪⋬   ⋠"))
  ("geq"  . ,(lean4-input-to-string-list "≥≧≳>≫⋙ ≷≻≽≿⊃⊇ ⋑⊐⊒ ⊱⊳⊵⋗⋛⋝⋟"))
  ("geqn" . ,(lean4-input-to-string-list "≱≩≯≵⋧ ≹  ⊁ ⋩⊅⊉⊋  ⋣⋥ ⋫⋭   ⋡"))

  ("<="   . ("≤"))  (">="   . ("≥"))
  ("<=n"  . ("≰"))  (">=n"  . ("≱"))
  ("len"  . ("≰"))  ("gen"  . ("≱"))
  ("<n"   . ("≮"))  (">n"   . ("≯"))
  ("<~"   . ("≲"))  (">~"   . ("≳"))
  ("<~n"  . ("⋦"))  (">~n"  . ("⋧"))
  ("<~nn" . ("≴"))  (">~nn" . ("≵"))

  ("ssub"   . ("⊂"))  ("ssup"   . ("⊃"))
  ("ssubn"  . ("⊄"))  ("ssupn"  . ("⊅"))
  ("sub"  . ("⊆")) ("sup"  . ("⊇"))
  ("subn" . ("⊈")) ("supn" . ("⊉"))
  ("ssqub"   . ("⊏"))  ("ssqup"   . ("⊐"))
  ("squb"  . ("⊑"))  ("squp"  . ("⊒"))
  ("squbn" . ("⋢"))  ("squpn" . ("⋣"))

  ;; Set membership etc.

  ("member" . ,(lean4-input-to-string-list "∈∉∊∋∌∍⋲⋳⋴⋵⋶⋷⋸⋹⋺⋻⋼⋽⋾⋿"))
  ("mem" . ("∈"))

  ("inn" . ("∉"))
  ("nin" . ("∌"))

  ;; Types

  ("T1" . ("Type₁"))
  ("T2" . ("Type₂"))
  ("T+" . ("Type₊"))

  ;; Intersections, unions etc.

  ("intersection" . ,(lean4-input-to-string-list "∩⋂∧⋀⋏⨇⊓⨅⋒∏ ⊼      ⨉"))
  ("union"        . ,(lean4-input-to-string-list "∪⋃∨⋁⋎⨈⊔⨆⋓∐⨿⊽⊻⊍⨃⊎⨄⊌∑⅀"))

  ("and" . ("∧"))  ("or"  . ("∨"))
  ("And" . ("⋀"))  ("Or"  . ("⋁"))
  ("i"   . ("∩"))  ("un"  . ("∪"))  ("u+" . ("⊎"))  ("u." . ("⊍"))
  ("I"   . ("⋂"))  ("Un"  . ("⋃"))  ("U+" . ("⨄"))  ("U." . ("⨃"))
  ("glb" . ("⊓"))  ("lub" . ("⊔"))
  ("Glb" . ("⨅"))  ("Lub" . ("⨆"))

  ;; Entailment etc.

  ("entails" . ,(lean4-input-to-string-list "⊢⊣⊤⊥⊦⊧⊨⊩⊪⊫⊬⊭⊮⊯"))

  ("|-"   . ("⊢"))  ("|-n"  . ("⊬"))
  ("-|"   . ("⊣"))
  ("|="   . ("⊨"))  ("|=n"  . ("⊭"))
  ("||-"  . ("⊩"))  ("||-n" . ("⊮"))
  ("||="  . ("⊫"))  ("||=n" . ("⊯"))
  ("|||-" . ("⊪"))

  ;; Divisibility, parallelity.

  ("|"  . ("∣"))  ("|n"  . ("∤"))
  ("||" . ("∥"))  ("||n" . ("∦"))

  ;; Some symbols from logic and set theory.

  ("all" . ("∀"))
  ("ex"  . ("∃"))
  ("exn" . ("∄"))
  ("0"   . ("∅"))
  ("empty"   . ("∅"))
  ("C"   . ("∁"))
  ("powerset" . ("𝒫"))

  ;; Corners, ceilings and floors.

  ("c"  . ,(lean4-input-to-string-list "⌜⌝⌞⌟⌈⌉⌊⌋"))
  ("cu" . ,(lean4-input-to-string-list "⌜⌝  ⌈⌉  "))
  ("cl" . ,(lean4-input-to-string-list "  ⌞⌟  ⌊⌋"))

  ("cul" . ("⌜"))  ("cuL" . ("⌈"))
  ("cur" . ("⌝"))  ("cuR" . ("⌉"))
  ("cll" . ("⌞"))  ("clL" . ("⌊"))
  ("clr" . ("⌟"))  ("clR" . ("⌋"))

  ;; Various operators/symbols.
  ("tr"        . ,(lean4-input-to-string-list "⬝▹"))
  ("trans"     . ,(lean4-input-to-string-list "▹⬝"))
  ("transport" . ("▹"))
  ("con"       . ("⬝"))
  ("dot"       . ("·"))
  ("sy"        . ("⁻¹"))
  ("inv"       . ("⁻¹"))
  ("-1"        . ("⁻¹" "₋₁"))
  ("-1e"       . ("⁻¹ᵉ"))
  ("-1f"       . ("⁻¹ᶠ"))
  ("-1g"       . ("⁻¹ᵍ"))
  ("-1h"       . ("⁻¹ʰ"))
  ("-1i"       . ("⁻¹ⁱ"))
  ("-1m"       . ("⁻¹ᵐ"))
  ("-1o"       . ("⁻¹ᵒ"))
  ("-1r"       . ("⁻¹ʳ"))
  ("-1p"       . ("⁻¹ᵖ"))
  ("-1s"       . ("⁻¹ˢ"))
  ("-1v"       . ("⁻¹ᵛ"))
  ("-1E"       . ("⁻¹ᴱ"))
  ("-2"        . ("⁻²" "₋₂"))
  ("-2o"       . ("⁻²ᵒ"))
  ("-3"        . ("⁻³"))
  ("qed"       . ("∎"))
  ("x"         . ("×"))
  ("o"         . ("∘"))
  ("comp"      . ("∘"))
  ("."         . ("·" "∙"))
  ("*"         . ("⋆"))
  (".+"        . ("∔"))
  (".-"        . ("∸"))
  (":"         . ("∶"))
  ("::"        . ("∷"))
  ("::-"       . ("∺"))
  ("-:"        . ("∹"))
  ("+ "        . ("⊹"))
  ("surd3"     . ("∛"))
  ("surd4"     . ("∜"))
  ("increment" . ("∆"))
  ("inf"       . ("∞"))
  ("&"         . ("⅋"))
  ("op"        . ("ᵒᵖ"))
  ("opf"       . ("ᵒᵖᶠ"))

  ;; Circled operators.

  ("o+"  . ("⊕"))
  ("o--" . ("⊖"))
  ("ox"  . ("⊗"))
  ("o/"  . ("⊘"))
  ("o."  . ("⊙"))
  ("oo"  . ("⊚"))
  ("o*"  . ("∘*" "⊛"))
  ("o="  . ("⊜"))
  ("o-"  . ("⊝"))

  ("O+"  . ("⨁"))
  ("Ox"  . ("⨂"))
  ("O."  . ("⨀"))
  ("O*"  . ("⍟"))

  ;; Boxed operators.

  ("b+" . ("⊞"))
  ("b-" . ("⊟"))
  ("bx" . ("⊠"))
  ("b." . ("⊡"))

  ;; Various symbols.

  ("integral" . ,(lean4-input-to-string-list "∫∬∭∮∯∰∱∲∳"))
  ("angle"    . ,(lean4-input-to-string-list "∟∡∢⊾⊿"))
  ("join"     . ,(lean4-input-to-string-list "⋈⋉⋊⋋⋌⨝⟕⟖⟗"))

  ;; Arrows.
  ("iff" . ("↔")) ("imp"  . ("→"))
  ("l"  . ,(lean4-input-to-string-list "←⇐⇚⇇⇆↤⇦↞↼↽⇠⇺↜⇽⟵⟸↚⇍⇷ ↹     ↢↩↫⇋⇜⇤⟻⟽⤆↶↺⟲                                     "))
  ("r"  . ,(lean4-input-to-string-list "→⇒⇛⇉⇄↦⇨↠⇀⇁⇢⇻↝⇾⟶⟹↛⇏⇸⇶ ↴    ↣↪↬⇌⇝⇥⟼⟾⤇↷↻⟳⇰⇴⟴⟿ ➵➸➙➔➛➜➝➞➟➠➡➢➣➤➧➨➩➪➫➬➭➮➯➱➲➳➺➻➼➽➾⊸"))
  ("u"  . ,(lean4-input-to-string-list "↑⇑⟰⇈⇅↥⇧↟↿↾⇡⇞          ↰↱➦ ⇪⇫⇬⇭⇮⇯                                           "))
  ("d"  . ,(lean4-input-to-string-list "↓⇓⟱⇊⇵↧⇩↡⇃⇂⇣⇟         ↵↲↳➥ ↯                                                "))
  ("ud" . ,(lean4-input-to-string-list "↕⇕   ↨⇳                                                                    "))
  ("lr" . ,(lean4-input-to-string-list "↔⇔         ⇼↭⇿⟷⟺↮⇎⇹                                                        "))
  ("ul" . ,(lean4-input-to-string-list "↖⇖                        ⇱↸                                               "))
  ("ur" . ,(lean4-input-to-string-list "↗⇗                                         ➶➹➚                             "))
  ("dr" . ,(lean4-input-to-string-list "↘⇘                        ⇲                ➴➷➘                             "))
  ("dl" . ,(lean4-input-to-string-list "↙⇙                                                                         "))
  ("==>" . ("⟹")) ("nattrans" . ("⟹")) ("nat_trans" . ("⟹"))

  ("l-"  . ("←"))  ("<-"  . ("←"))  ("l="  . ("⇐"))
  ("r-"  . ("→"))  ("->"  . ("→"))  ("r="  . ("⇒"))  ("=>"  . ("⇒")) ("functor"  . ("⇒"))
  ("u-"  . ("↑"))                   ("u="  . ("⇑"))
  ("d-"  . ("↓"))                   ("d="  . ("⇓"))
  ("ud-" . ("↕"))                   ("ud=" . ("⇕"))
  ("lr-" . ("↔"))  ("<->" . ("↔"))  ("lr=" . ("⇔"))  ("<=>" . ("⇔"))
  ("ul-" . ("↖"))                   ("ul=" . ("⇖"))
  ("ur-" . ("↗"))                   ("ur=" . ("⇗"))
  ("dr-" . ("↘"))                   ("dr=" . ("⇘"))
  ("dl-" . ("↙"))                   ("dl=" . ("⇙"))

  ("l==" . ("⇚"))  ("l-2" . ("⇇"))                   ("l-r-" . ("⇆"))
  ("r==" . ("⇛"))  ("r-2" . ("⇉"))  ("r-3" . ("⇶"))  ("r-l-" . ("⇄"))
  ("u==" . ("⟰"))  ("u-2" . ("⇈"))                   ("u-d-" . ("⇅"))
  ("d==" . ("⟱"))  ("d-2" . ("⇊"))                   ("d-u-" . ("⇵"))

  ("l--"  . ("⟵"))  ("<--"  . ("⟵"))  ("l~"  . ("↜" "⇜"))
  ("r--"  . ("⟶"))  ("-->"  . ("⟶"))  ("r~"  . ("↝" "⇝" "⟿")) ("hom"  . ("⟶"))
  ("lr--" . ("⟷"))  ("<-->" . ("⟷"))  ("lr~" . ("↭"))

  ("l-n"  . ("↚"))  ("<-n"  . ("↚"))  ("l=n"  . ("⇍"))
  ("r-n"  . ("↛"))  ("->n"  . ("↛"))  ("r=n"  . ("⇏"))  ("=>n"  . ("⇏"))
  ("lr-n" . ("↮"))  ("<->n" . ("↮"))  ("lr=n" . ("⇎"))  ("<=>n" . ("⇎"))

  ("l-|"  . ("↤"))  ("ll-" . ("↞"))
  ("r-|"  . ("↦"))  ("rr-" . ("↠"))
  ("u-|"  . ("↥"))  ("uu-" . ("↟"))
  ("d-|"  . ("↧"))  ("dd-" . ("↡"))
  ("ud-|" . ("↨"))

  ("l->" . ("↢"))
  ("r->" . ("↣"))

  ("r-o" . ("⊸"))  ("-o"  . ("⊸"))

  ("dz" . ("↯"))

  ;; Ellipsis.

  ("..." . ,(lean4-input-to-string-list "⋯⋮⋰⋱"))

  ;; Box-drawing characters.

  ("---" . ,(lean4-input-to-string-list "─│┌┐└┘├┤┬┼┴╴╵╶╷╭╮╯╰╱╲╳"))
  ("--=" . ,(lean4-input-to-string-list "═║╔╗╚╝╠╣╦╬╩     ╒╕╘╛╞╡╤╪╧ ╓╖╙╜╟╢╥╫╨"))
  ("--_" . ,(lean4-input-to-string-list "━┃┏┓┗┛┣┫┳╋┻╸╹╺╻
                                        ┍┯┑┕┷┙┝┿┥┎┰┒┖┸┚┠╂┨┞╀┦┟╁┧┢╈┪┡╇┩
                                        ┮┭┶┵┾┽┲┱┺┹╊╉╆╅╄╃ ╿╽╼╾"))
  ("--." . ,(lean4-input-to-string-list "╌╎┄┆┈┊
                                        ╍╏┅┇┉┋"))

  ;; Triangles.

  ;; Big/small, black/white.

  ("t"     . ,(lean4-input-to-string-list "▸▹►▻◂◃◄◅▴▵▾▿◢◿◣◺◤◸◥◹"))
  ("Tr"    . ,(lean4-input-to-string-list "◀◁▶▷▲△▼▽◬◭◮"))

  ("tb" . ,(lean4-input-to-string-list "◂▸▴▾◄►◢◣◤◥"))
  ("tw" . ,(lean4-input-to-string-list "◃▹▵▿◅▻◿◺◸◹"))

  ("Tb" . ,(lean4-input-to-string-list "◀▶▲▼"))
  ("Tw" . ,(lean4-input-to-string-list "◁▷△▽"))

  ;; Squares.

  ("sq"  . ,(lean4-input-to-string-list "◾◽■□◼◻▣▢▤▥▦▧▨▩◧◨◩◪◫◰◱◲◳"))
  ("sqb" . ,(lean4-input-to-string-list "■◼◾"))
  ("sqw" . ,(lean4-input-to-string-list "□◻◽"))
  ("sq." . ("▣"))
  ("sqo" . ("▢"))

  ;; Rectangles.

  ("re"  . ,(lean4-input-to-string-list "▬▭▮▯"))
  ("reb" . ,(lean4-input-to-string-list "▬▮"))
  ("rew" . ,(lean4-input-to-string-list "▭▯"))

  ;; Parallelograms.

  ("pa"  . ,(lean4-input-to-string-list "▰▱"))
  ("pab" . ("▰"))
  ("paw" . ("▱"))

  ;; Diamonds.

  ("di"  . ,(lean4-input-to-string-list "◆◇◈"))
  ("dib" . ("◆"))
  ("diw" . ("◇"))
  ("di." . ("◈"))

  ;; Circles.

  ("ci"   . ,(lean4-input-to-string-list "●○◎◌◯◍◐◑◒◓◔◕◖◗◠◡◴◵◶◷⚆⚇⚈⚉"))
  ("cib"  . ("●"))
  ("ciw"  . ("○"))
  ("ci."  . ("◎"))
  ("ci.." . ("◌"))
  ("ciO"  . ("◯"))

  ;; Stars.

  ("st"   . ,(lean4-input-to-string-list "⋆✦✧✶✴✹ ★☆✪✫✯✰✵✷✸"))
  ("st4"  . ,(lean4-input-to-string-list "✦✧"))
  ("st6"  . ("✶"))
  ("st8"  . ("✴"))
  ("st12" . ("✹"))

  ;; Blackboard bold letters.

  ("bn"   . ("ℕ"))
  ("bz"   . ("ℤ"))
  ("bq"   . ("ℚ"))
  ("br"   . ("ℝ"))
  ("bc"   . ("ℂ"))
  ("bp"   . ("ℙ"))
  ("bb"   . ("𝔹"))
  ("bsum" . ("⅀"))

  ;; Blackboard bold numbers.

  ("b0"   . ("𝟘"))
  ("b1"   . ("𝟙"))
  ("b2"   . ("𝟚"))
  ("b3"   . ("𝟛"))
  ("b4"   . ("𝟜"))
  ("b5"   . ("𝟝"))
  ("b6"   . ("𝟞"))
  ("b7"   . ("𝟟"))
  ("b8"   . ("𝟠"))
  ("b9"   . ("𝟡"))

  ;; Parentheses.

  ("(" . ,(lean4-input-to-string-list "([{⁅⁽₍〈⎴⟅⟦⟨⟪⦃〈《‹«「『【〔〖〚︵︷︹︻︽︿﹁﹃﹙﹛﹝（［｛｢"))
  (")" . ,(lean4-input-to-string-list ")]}⁆⁾₎〉⎵⟆⟧⟩⟫⦄〉》›»」』】〕〗〛︶︸︺︼︾﹀﹂﹄﹚﹜﹞）］｝｣"))

  ("[[" . ("⟦"))
  ("]]" . ("⟧"))
  ("<"  . ("⟨"))
  (">"  . ("⟩"))
  ("<<" . ("⟪"))
  (">>" . ("⟫"))
  ("f<"  . ("‹"))
  ("f>"  . ("›"))
  ("f<<" . ("«"))
  ("f>>" . ("»"))
  ("{{" . ("⦃"))
  ("}}" . ("⦄"))

  ("(b" . ("⟅"))
  (")b" . ("⟆"))

  ("lbag" . ("⟅"))
  ("rbag" . ("⟆"))

  ;; lambda

  ("fun" . ("λ"))
  ("lam" . ("λ"))

  ("X" . ("⨯"))

  ;; Primes.

  ("'" . ,(lean4-input-to-string-list "′″‴⁗"))
  ("`" . ,(lean4-input-to-string-list "‵‶‷"))

  ;; Fractions.

  ("frac" . ,(lean4-input-to-string-list "¼½¾⅓⅔⅕⅖⅗⅘⅙⅚⅛⅜⅝⅞⅟"))

  ;; Bullets.

  ("bu"  . ,(lean4-input-to-string-list "•◦‣⁌⁍"))
  ("bub" . ("•"))
  ("buw" . ("◦"))
  ("but" . ("‣"))

  ;; Types
  ("nat"  . ("ℕ"))
  ("Nat"  . ("ℕ"))
  ("N"    . ("ℕ"))
  ("N-2"  . ("ℕ₋₂"))
  ("N-1"  . ("ℕ₋₁"))
  ("int"  . ("ℤ"))
  ("Int"  . ("ℤ"))
  ("Z"    . ("ℤ"))
  ("rat"  . ("ℚ"))
  ("Rat"  . ("ℚ"))
  ("Q"    . ("ℚ"))
  ("real" . ("ℝ"))
  ("Real" . ("ℝ"))
  ("R"    . ("ℝ"))
  ("Com"  . ("ℂ"))
  ("com"  . ("ℂ"))
  ("C"    . ("ℂ"))
  ("A"    . ("𝔸"))
  ("F"    . ("𝔽"))
  ("H"    . ("ℍ"))
  ("K"    . ("𝕂"))

  ("a" . ("α"))
  ("b" . ("β"))
  ("g" . ("γ"))

  ;; Musical symbols.

  ("note" . ,(lean4-input-to-string-list "♩♪♫♬"))
  ("flat" . ("♭"))
  ("#"    . ("♯"))

  ;; Other punctuation and symbols.

  ("\\"         . ("\\"))
  ("en"         . ("–"))
  ("em"         . ("—"))
  ("^i"         . ("ⁱ"))
  ("^o"         . ("ᵒ"))
  ("!!"         . ("‼"))
  ("??"         . ("⁇"))
  ("?!"         . ("‽" "⁈"))
  ("!?"         . ("⁉"))
  ("die"        . ,(lean4-input-to-string-list "⚀⚁⚂⚃⚄⚅"))
  ("asterisk"   . ,(lean4-input-to-string-list "⁎⁑⁂✢✣✤✥✱✲✳✺✻✼✽❃❉❊❋"))
  ("8<"         . ("✂" "✄"))
  ("tie"        . ("⁀"))
  ("undertie"   . ("‿"))
  ("apl"        . ,(lean4-input-to-string-list "⌶⌷⌸⌹⌺⌻⌼⌽⌾⌿⍀⍁⍂⍃⍄⍅⍆⍇⍈
                                               ⍉⍊⍋⍌⍍⍎⍏⍐⍑⍒⍓⍔⍕⍖⍗⍘⍙⍚⍛
                                               ⍜⍝⍞⍟⍠⍡⍢⍣⍤⍥⍦⍧⍨⍩⍪⍫⍬⍭⍮
                                               ⍯⍰⍱⍲⍳⍴⍵⍶⍷⍸⍹⍺⎕"))

  ;; Some combining characters.
  ;;
  ;; The following combining characters also have (other)
  ;; translations:
  ;; ̀ ́ ̂ ̃ ̄ ̆ ̇ ̈ ̋ ̌ ̣ ̧ ̱

  ("^--" . ,(lean4-input-to-string-list"̅̿"))
  ("_--" . ,(lean4-input-to-string-list"̲̳"))
  ("^~"  . ,(lean4-input-to-string-list"̃͌"))
  ("_~"  .  (                         "̰"))
  ("^."  . ,(lean4-input-to-string-list"̇̈⃛⃜"))
  ("_."  . ,(lean4-input-to-string-list"̣̤"))
  ("^l"  . ,(lean4-input-to-string-list"⃖⃐⃔"))
  ("^l-" .  (                         "⃖"))
  ("^r"  . ,(lean4-input-to-string-list"⃗⃑⃕"))
  ("^r-" .  (                         "⃗"))
  ("^lr" .  (                         "⃡"))
  ("_lr" .  (                         "͍"))
  ("^^"  . ,(lean4-input-to-string-list"̂̑͆"))
  ("_^"  . ,(lean4-input-to-string-list"̭̯̪"))
  ("^v"  . ,(lean4-input-to-string-list"̌̆"))
  ("_v"  . ,(lean4-input-to-string-list"̬̮̺"))

  ;; Shorter forms of many greek letters plus ƛ.

  ("Ga"  . ("α"))  ("GA"  . ("Α"))
  ("Gb"  . ("β"))  ("GB"  . ("Β"))
  ("Gg"  . ("γ"))  ("GG"  . ("Γ"))
  ("Gd"  . ("δ"))  ("GD"  . ("Δ"))
  ("Ge"  . ("ε"))  ("GE"  . ("Ε"))  ("eps" . ("ε"))
  ("Gz"  . ("ζ"))  ("GZ"  . ("Ζ"))
  ;; \eta \Eta
  ("Gth" . ("θ"))  ("GTH" . ("Θ"))  ("th"  . ("θ"))
  ("Gi"  . ("ι"))  ("GI"  . ("Ι"))
  ("Gk"  . ("κ"))  ("GK"  . ("Κ"))
  ("Gl"  . ("λ"))  ("GL"  . ("Λ"))  ("Gl-" . ("ƛ"))
  ("Gm"  . ("μ"))  ("GM"  . ("Μ"))
  ("Gn"  . ("ν"))  ("GN"  . ("Ν"))
  ("Gx"  . ("ξ"))  ("GX"  . ("Ξ"))
  ;; \omicron \Omicron
  ;; \pi \Pi
  ("Gr"  . ("ρ"))  ("GR"  . ("Ρ"))
  ("Gs"  . ("σ"))  ("GS"  . ("Σ"))
  ("Gt"  . ("τ"))  ("GT"  . ("Τ"))
  ("Gu"  . ("υ"))  ("GU"  . ("Υ"))
  ("Gf"  . ("φ"))  ("GF"  . ("Φ"))
  ("Gc"  . ("χ"))  ("GC"  . ("Χ"))
  ("Gp"  . ("ψ"))  ("GP"  . ("Ψ"))
  ("Go"  . ("ω"))  ("GO"  . ("Ω"))
  ;; even shorter versions for central type constructors
  ("S"   . ("Σ"))  ("P"   . ("Π"))

  ;; Mathematical characters

  ("MiA" . ("𝐴"))
  ("MiB" . ("𝐵"))
  ("MiC" . ("𝐶"))
  ("MiD" . ("𝐷"))
  ("MiE" . ("𝐸"))
  ("MiF" . ("𝐹"))
  ("MiG" . ("𝐺"))
  ("MiH" . ("𝐻"))
  ("MiI" . ("𝐼"))
  ("MiJ" . ("𝐽"))
  ("MiK" . ("𝐾"))
  ("MiL" . ("𝐿"))
  ("MiM" . ("𝑀"))
  ("MiN" . ("𝑁"))
  ("MiO" . ("𝑂"))
  ("MiP" . ("𝑃"))
  ("MiQ" . ("𝑄"))
  ("MiR" . ("𝑅"))
  ("MiS" . ("𝑆"))
  ("MiT" . ("𝑇"))
  ("MiU" . ("𝑈"))
  ("MiV" . ("𝑉"))
  ("MiW" . ("𝑊"))
  ("MiX" . ("𝑋"))
  ("MiY" . ("𝑌"))
  ("MiZ" . ("𝑍"))
  ("Mia" . ("𝑎"))
  ("Mib" . ("𝑏"))
  ("Mic" . ("𝑐"))
  ("Mid" . ("𝑑"))
  ("Mie" . ("𝑒"))
  ("Mif" . ("𝑓"))
  ("Mig" . ("𝑔"))
  ("Mih" . ("ℎ"))
  ("Mii" . ("𝑖"))
  ("Mij" . ("𝑗"))
  ("Mik" . ("𝑘"))
  ("Mil" . ("𝑙"))
  ("Mim" . ("𝑚"))
  ("Min" . ("𝑛"))
  ("Mio" . ("𝑜"))
  ("Mip" . ("𝑝"))
  ("Miq" . ("𝑞"))
  ("Mir" . ("𝑟"))
  ("Mis" . ("𝑠"))
  ("Mit" . ("𝑡"))
  ("Miu" . ("𝑢"))
  ("Miv" . ("𝑣"))
  ("Miw" . ("𝑤"))
  ("Mix" . ("𝑥"))
  ("Miy" . ("𝑦"))
  ("Miz" . ("𝑧"))
  ("MIA" . ("𝑨"))
  ("MIB" . ("𝑩"))
  ("MIC" . ("𝑪"))
  ("MID" . ("𝑫"))
  ("MIE" . ("𝑬"))
  ("MIF" . ("𝑭"))
  ("MIG" . ("𝑮"))
  ("MIH" . ("𝑯"))
  ("MII" . ("𝑰"))
  ("MIJ" . ("𝑱"))
  ("MIK" . ("𝑲"))
  ("MIL" . ("𝑳"))
  ("MIM" . ("𝑴"))
  ("MIN" . ("𝑵"))
  ("MIO" . ("𝑶"))
  ("MIP" . ("𝑷"))
  ("MIQ" . ("𝑸"))
  ("MIR" . ("𝑹"))
  ("MIS" . ("𝑺"))
  ("MIT" . ("𝑻"))
  ("MIU" . ("𝑼"))
  ("MIV" . ("𝑽"))
  ("MIW" . ("𝑾"))
  ("MIX" . ("𝑿"))
  ("MIY" . ("𝒀"))
  ("MIZ" . ("𝒁"))
  ("MIa" . ("𝒂"))
  ("MIb" . ("𝒃"))
  ("MIc" . ("𝒄"))
  ("MId" . ("𝒅"))
  ("MIe" . ("𝒆"))
  ("MIf" . ("𝒇"))
  ("MIg" . ("𝒈"))
  ("MIh" . ("𝒉"))
  ("MIi" . ("𝒊"))
  ("MIj" . ("𝒋"))
  ("MIk" . ("𝒌"))
  ("MIl" . ("𝒍"))
  ("MIm" . ("𝒎"))
  ("MIn" . ("𝒏"))
  ("MIo" . ("𝒐"))
  ("MIp" . ("𝒑"))
  ("MIq" . ("𝒒"))
  ("MIr" . ("𝒓"))
  ("MIs" . ("𝒔"))
  ("MIt" . ("𝒕"))
  ("MIu" . ("𝒖"))
  ("MIv" . ("𝒗"))
  ("MIw" . ("𝒘"))
  ("MIx" . ("𝒙"))
  ("MIy" . ("𝒚"))
  ("MIz" . ("𝒛"))
  ("McA" . ("𝒜"))
  ("McB" . ("ℬ"))
  ("McC" . ("𝒞"))
  ("McD" . ("𝒟"))
  ("McE" . ("ℰ"))
  ("McF" . ("ℱ"))
  ("McG" . ("𝒢"))
  ("McH" . ("ℋ"))
  ("McI" . ("ℐ"))
  ("McJ" . ("𝒥"))
  ("McK" . ("𝒦"))
  ("McL" . ("ℒ"))
  ("McM" . ("ℳ"))
  ("McN" . ("𝒩"))
  ("McO" . ("𝒪"))
  ("McP" . ("𝒫"))
  ("McQ" . ("𝒬"))
  ("McR" . ("ℛ"))
  ("McS" . ("𝒮"))
  ("McT" . ("𝒯"))
  ("McU" . ("𝒰"))
  ("McV" . ("𝒱"))
  ("McW" . ("𝒲"))
  ("McX" . ("𝒳"))
  ("McY" . ("𝒴"))
  ("McZ" . ("𝒵"))
  ("Mca" . ("𝒶"))
  ("Mcb" . ("𝒷"))
  ("Mcc" . ("𝒸"))
  ("Mcd" . ("𝒹"))
  ("Mce" . ("ℯ"))
  ("Mcf" . ("𝒻"))
  ("Mcg" . ("ℊ"))
  ("Mch" . ("𝒽"))
  ("Mci" . ("𝒾"))
  ("Mcj" . ("𝒿"))
  ("Mck" . ("𝓀"))
  ("Mcl" . ("𝓁"))
  ("Mcm" . ("𝓂"))
  ("Mcn" . ("𝓃"))
  ("Mco" . ("ℴ"))
  ("Mcp" . ("𝓅"))
  ("Mcq" . ("𝓆"))
  ("Mcr" . ("𝓇"))
  ("Mcs" . ("𝓈"))
  ("Mct" . ("𝓉"))
  ("Mcu" . ("𝓊"))
  ("Mcv" . ("𝓋"))
  ("Mcw" . ("𝓌"))
  ("Mcx" . ("𝓍"))
  ("Mcy" . ("𝓎"))
  ("Mcz" . ("𝓏"))
  ("MCA" . ("𝓐"))
  ("MCB" . ("𝓑"))
  ("MCC" . ("𝓒"))
  ("MCD" . ("𝓓"))
  ("MCE" . ("𝓔"))
  ("MCF" . ("𝓕"))
  ("MCG" . ("𝓖"))
  ("MCH" . ("𝓗"))
  ("MCI" . ("𝓘"))
  ("MCJ" . ("𝓙"))
  ("MCK" . ("𝓚"))
  ("MCL" . ("𝓛"))
  ("MCM" . ("𝓜"))
  ("MCN" . ("𝓝"))
  ("MCO" . ("𝓞"))
  ("MCP" . ("𝓟"))
  ("MCQ" . ("𝓠"))
  ("MCR" . ("𝓡"))
  ("MCS" . ("𝓢"))
  ("MCT" . ("𝓣"))
  ("MCU" . ("𝓤"))
  ("MCV" . ("𝓥"))
  ("MCW" . ("𝓦"))
  ("MCX" . ("𝓧"))
  ("MCY" . ("𝓨"))
  ("MCZ" . ("𝓩"))
  ("MCa" . ("𝓪"))
  ("MCb" . ("𝓫"))
  ("MCc" . ("𝓬"))
  ("MCd" . ("𝓭"))
  ("MCe" . ("𝓮"))
  ("MCf" . ("𝓯"))
  ("MCg" . ("𝓰"))
  ("MCh" . ("𝓱"))
  ("MCi" . ("𝓲"))
  ("MCj" . ("𝓳"))
  ("MCk" . ("𝓴"))
  ("MCl" . ("𝓵"))
  ("MCm" . ("𝓶"))
  ("MCn" . ("𝓷"))
  ("MCo" . ("𝓸"))
  ("MCp" . ("𝓹"))
  ("MCq" . ("𝓺"))
  ("MCr" . ("𝓻"))
  ("MCs" . ("𝓼"))
  ("MCt" . ("𝓽"))
  ("MCu" . ("𝓾"))
  ("MCv" . ("𝓿"))
  ("MCw" . ("𝔀"))
  ("MCx" . ("𝔁"))
  ("MCy" . ("𝔂"))
  ("MCz" . ("𝔃"))
  ("MfA" . ("𝔄"))
  ("MfB" . ("𝔅"))
  ("MfC" . ("ℭ"))
  ("MfD" . ("𝔇"))
  ("MfE" . ("𝔈"))
  ("MfF" . ("𝔉"))
  ("MfG" . ("𝔊"))
  ("MfH" . ("ℌ"))
  ("MfI" . ("ℑ"))
  ("MfJ" . ("𝔍"))
  ("MfK" . ("𝔎"))
  ("MfL" . ("𝔏"))
  ("MfM" . ("𝔐"))
  ("MfN" . ("𝔑"))
  ("MfO" . ("𝔒"))
  ("MfP" . ("𝔓"))
  ("MfQ" . ("𝔔"))
  ("MfR" . ("ℜ"))
  ("MfS" . ("𝔖"))
  ("MfT" . ("𝔗"))
  ("MfU" . ("𝔘"))
  ("MfV" . ("𝔙"))
  ("MfW" . ("𝔚"))
  ("MfX" . ("𝔛"))
  ("MfY" . ("𝔜"))
  ("MfZ" . ("ℨ"))
  ("Mfa" . ("𝔞"))
  ("Mfb" . ("𝔟"))
  ("Mfc" . ("𝔠"))
  ("Mfd" . ("𝔡"))
  ("Mfe" . ("𝔢"))
  ("Mff" . ("𝔣"))
  ("Mfg" . ("𝔤"))
  ("Mfh" . ("𝔥"))
  ("Mfi" . ("𝔦"))
  ("Mfj" . ("𝔧"))
  ("Mfk" . ("𝔨"))
  ("Mfl" . ("𝔩"))
  ("Mfm" . ("𝔪"))
  ("Mfn" . ("𝔫"))
  ("Mfo" . ("𝔬"))
  ("Mfp" . ("𝔭"))
  ("Mfq" . ("𝔮"))
  ("Mfr" . ("𝔯"))
  ("Mfs" . ("𝔰"))
  ("Mft" . ("𝔱"))
  ("Mfu" . ("𝔲"))
  ("Mfv" . ("𝔳"))
  ("Mfw" . ("𝔴"))
  ("Mfx" . ("𝔵"))
  ("Mfy" . ("𝔶"))
  ("Mfz" . ("𝔷"))

  ;; Some ISO8859-1 characters.

  (" "         . (" "))
  ("!"         . ("¡"))
  ("cent"      . ("¢"))
  ("brokenbar" . ("¦"))
  ("degree"    . ("°"))
  ("?"         . ("¿"))
  ("^a_"       . ("ª"))
  ("^o_"       . ("º"))

  ;; Circled, parenthesised etc. numbers and letters.

  ( "(0)" . ,(lean4-input-to-string-list " ⓪"))
  ( "(1)" . ,(lean4-input-to-string-list "⑴①⒈❶➀➊"))
  ( "(2)" . ,(lean4-input-to-string-list "⑵②⒉❷➁➋"))
  ( "(3)" . ,(lean4-input-to-string-list "⑶③⒊❸➂➌"))
  ( "(4)" . ,(lean4-input-to-string-list "⑷④⒋❹➃➍"))
  ( "(5)" . ,(lean4-input-to-string-list "⑸⑤⒌❺➄➎"))
  ( "(6)" . ,(lean4-input-to-string-list "⑹⑥⒍❻➅➏"))
  ( "(7)" . ,(lean4-input-to-string-list "⑺⑦⒎❼➆➐"))
  ( "(8)" . ,(lean4-input-to-string-list "⑻⑧⒏❽➇➑"))
  ( "(9)" . ,(lean4-input-to-string-list "⑼⑨⒐❾➈➒"))
  ("(10)" . ,(lean4-input-to-string-list "⑽⑩⒑❿➉➓"))
  ("(11)" . ,(lean4-input-to-string-list "⑾⑪⒒"))
  ("(12)" . ,(lean4-input-to-string-list "⑿⑫⒓"))
  ("(13)" . ,(lean4-input-to-string-list "⒀⑬⒔"))
  ("(14)" . ,(lean4-input-to-string-list "⒁⑭⒕"))
  ("(15)" . ,(lean4-input-to-string-list "⒂⑮⒖"))
  ("(16)" . ,(lean4-input-to-string-list "⒃⑯⒗"))
  ("(17)" . ,(lean4-input-to-string-list "⒄⑰⒘"))
  ("(18)" . ,(lean4-input-to-string-list "⒅⑱⒙"))
  ("(19)" . ,(lean4-input-to-string-list "⒆⑲⒚"))
  ("(20)" . ,(lean4-input-to-string-list "⒇⑳⒛"))

  ("(a)"  . ,(lean4-input-to-string-list "⒜Ⓐⓐ"))
  ("(b)"  . ,(lean4-input-to-string-list "⒝Ⓑⓑ"))
  ("(c)"  . ,(lean4-input-to-string-list "⒞Ⓒⓒ"))
  ("(d)"  . ,(lean4-input-to-string-list "⒟Ⓓⓓ"))
  ("(e)"  . ,(lean4-input-to-string-list "⒠Ⓔⓔ"))
  ("(f)"  . ,(lean4-input-to-string-list "⒡Ⓕⓕ"))
  ("(g)"  . ,(lean4-input-to-string-list "⒢Ⓖⓖ"))
  ("(h)"  . ,(lean4-input-to-string-list "⒣Ⓗⓗ"))
  ("(i)"  . ,(lean4-input-to-string-list "⒤Ⓘⓘ"))
  ("(j)"  . ,(lean4-input-to-string-list "⒥Ⓙⓙ"))
  ("(k)"  . ,(lean4-input-to-string-list "⒦Ⓚⓚ"))
  ("(l)"  . ,(lean4-input-to-string-list "⒧Ⓛⓛ"))
  ("(m)"  . ,(lean4-input-to-string-list "⒨Ⓜⓜ"))
  ("(n)"  . ,(lean4-input-to-string-list "⒩Ⓝⓝ"))
  ("(o)"  . ,(lean4-input-to-string-list "⒪Ⓞⓞ"))
  ("(p)"  . ,(lean4-input-to-string-list "⒫Ⓟⓟ"))
  ("(q)"  . ,(lean4-input-to-string-list "⒬Ⓠⓠ"))
  ("(r)"  . ,(lean4-input-to-string-list "⒭Ⓡⓡ"))
  ("(s)"  . ,(lean4-input-to-string-list "⒮Ⓢⓢ"))
  ("(t)"  . ,(lean4-input-to-string-list "⒯Ⓣⓣ"))
  ("(u)"  . ,(lean4-input-to-string-list "⒰Ⓤⓤ"))
  ("(v)"  . ,(lean4-input-to-string-list "⒱Ⓥⓥ"))
  ("(w)"  . ,(lean4-input-to-string-list "⒲Ⓦⓦ"))
  ("(x)"  . ,(lean4-input-to-string-list "⒳Ⓧⓧ"))
  ("(y)"  . ,(lean4-input-to-string-list "⒴Ⓨⓨ"))
  ("(z)"  . ,(lean4-input-to-string-list "⒵Ⓩⓩ"))
  ("y"    . ("ɏ"))


  ))
  "A list of translations specific to the Lean input method.
Each element is a pair (KEY-SEQUENCE-STRING . LIST-OF-TRANSLATION-STRINGS).
All the translation strings are possible translations
of the given key sequence; if there is more than one you can choose
between them using the arrow keys.

Note that if you customize this setting you will not
automatically benefit (or suffer) from modifications to its
default value when the library is updated.  If you just want to
add some bindings it is probably a better idea to customize
`lean4-input-user-translations'.

These translation pairs are included after those in
`lean4-input-user-translations', but before the ones inherited
from other input methods (see `lean4-input-inherit').

If you change this setting manually (without using the
customization buffer) you need to call `lean4-input-setup' in
order for the change to take effect."
  :group 'lean4-input
  :set 'lean4-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type '(repeat (cons (string :tag "Key sequence")
                       (repeat :tag "Translations" string))))

(defcustom lean4-input-user-translations nil
  "Like `lean4-input-translations', but more suitable for user
customizations since by default it is empty.

These translation pairs are included first, before those in
`lean4-input-translations' and the ones inherited from other input
methods."
  :group 'lean4-input
  :set 'lean4-input-incorporate-changed-setting
  :initialize 'custom-initialize-default
  :type '(repeat (cons (string :tag "Key sequence")
                       (repeat :tag "Translations" string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inspecting and modifying translation maps

(defun lean4-input-get-translations (qp)
  "Return a list containing all translations from the Quail
package QP (except for those corresponding to ASCII).
Each pair in the list has the form (KEY-SEQUENCE . TRANSLATION)."
  (with-temp-buffer
    (activate-input-method qp) ; To make sure that the package is loaded.
    (unless (quail-package qp)
      (error "%s is not a Quail package." qp))
    (let ((decode-map (list 'decode-map)))
      (quail-build-decode-map (list (quail-map)) "" decode-map 0)
      (cdr decode-map))))

(defun lean4-input-show-translations (qp)
  "Display all translations used by the Quail package QP (a string).
\(Except for those corresponding to ASCII)."
  (interactive (list (read-input-method-name
                      "Quail input method (default %s): " "Lean")))
  (let ((buf (concat "*" qp " input method translations*")))
    (with-output-to-temp-buffer buf
      (with-current-buffer buf
        (quail-insert-decode-map
         (cons 'decode-map (lean4-input-get-translations qp)))))))

(defun lean4-input-add-translations (trans)
  "Add the given translations TRANS to the Lean input method.
TRANS is a list of pairs (KEY-SEQUENCE . TRANSLATION). The
translations are appended to the current translations."
  (with-temp-buffer
    (dolist (tr (lean4-input-concat-map (eval lean4-input-tweak-all) trans))
      (quail-defrule (car tr) (cdr tr) "Lean" t))))

(defun lean4-input-inherit-package (qp &optional fun)
  "Let the Lean input method inherit the translations from the
Quail package QP (except for those corresponding to ASCII).

The optional function FUN can be used to modify the translations.
It is given a pair (KEY-SEQUENCE . TRANSLATION) and should return
a list of such pairs."
  (let ((trans (lean4-input-get-translations qp)))
    (lean4-input-add-translations
     (if fun (lean4-input-concat-map fun trans)
       trans))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Setting up the input method

(defun lean4-input-setup ()
  "Set up the Lean input method based on the customisable
variables and underlying input methods."

  ;; Create (or reset) the input method.
  (with-temp-buffer
    (quail-define-package "Lean" "UTF-8" "∏" t ; guidance
     "Lean input method.
The purpose of this input method is to edit Lean programs, but
since it is highly customisable it can be made useful for other
tasks as well."
     nil nil nil nil nil nil t ; maximum-shortest
     ))

  (lean4-input-add-translations
   (mapcar (lambda (tr) (cons (car tr) (vconcat (cdr tr))))
           (append lean4-input-user-translations
                   lean4-input-translations)))
  (dolist (def lean4-input-inherit)
    (lean4-input-inherit-package (car def)
                                (eval (cdr def)))))

(defun lean4-input-incorporate-changed-setting (sym val)
  "Update the Lean input method based on the customisable
variables and underlying input methods.
Suitable for use in the :set field of `defcustom'."
  (set-default sym val)
  (lean4-input-setup))

;; Set up the input method.

(lean4-input-setup)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Administrative details

(provide 'lean4-input)
;;; lean4-input.el ends here

(defun lean4-input-export-translations ()
  "Export the current translation, (input, output) pairs for
input-method, in a javascript format. It can be copy-pasted to
leanprover.github.io/tutorial/js/input-method.js"
  (interactive)
  (with-current-buffer
      (get-buffer-create "*lean4-translations*")
    (let ((exclude-list '("\\newline")))
      (insert "var corrections = {")
      (--each
          (--filter (not (member (car it) exclude-list))
                    (lean4-input-get-translations "Lean"))
        (let* ((input (substring (car it) 1))
               (outputs (cdr it)))
          (insert (format "%s:\"" (prin1-to-string input)))
          (cond ((vectorp outputs)
                 (insert (elt outputs 0)))
                (t (insert-char outputs)))
          (insert (format "\",\n" input))))
      (insert "};"))))

(defun lean4-input-export-translations-to-stdout ()
  (lean4-input-export-translations)
  (with-current-buffer "*lean4-translations*"
    (princ (buffer-string))))
