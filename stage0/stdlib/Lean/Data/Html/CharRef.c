// Lean compiler output
// Module: Lean.Data.Html.CharRef
// Imports: public import Init.Prelude import Init.While import Init.Data.Array.BinSearch import Init.Data.String.Basic import Lean.Data.Html.Spec
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t l_Lean_Html_isNonCharacter(uint32_t);
uint8_t l_Lean_Html_isControl(uint32_t);
uint8_t l_Lean_Html_isAsciiWhitespace(uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static const lean_string_object l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharRefData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24470, .m_capacity = 24470, .m_length = 20471, .m_data = "AElig Æ AMP & Aacute Á Abreve Ă Acirc Â Acy А Afr 𝔄 Agrave À Alpha Α Amacr Ā And ⩓ Aogon Ą Aopf 𝔸 ApplyFunction ⁡ Aring Å Ascr 𝒜 Assign ≔ Atilde Ã Auml Ä Backslash ∖ Barv ⫧ Barwed ⌆ Bcy Б Because ∵ Bernoullis ℬ Beta Β Bfr 𝔅 Bopf 𝔹 Breve ˘ Bscr ℬ Bumpeq ≎ CHcy Ч COPY © Cacute Ć Cap ⋒ CapitalDifferentialD ⅅ Cayleys ℭ Ccaron Č Ccedil Ç Ccirc Ĉ Cconint ∰ Cdot Ċ Cedilla ¸ CenterDot · Cfr ℭ Chi Χ CircleDot ⊙ CircleMinus ⊖ CirclePlus ⊕ CircleTimes ⊗ ClockwiseContourIntegral ∲ CloseCurlyDoubleQuote ” CloseCurlyQuote ’ Colon ∷ Colone ⩴ Congruent ≡ Conint ∯ ContourIntegral ∮ Copf ℂ Coproduct ∐ CounterClockwiseContourIntegral ∳ Cross ⨯ Cscr 𝒞 Cup ⋓ CupCap ≍ DD ⅅ DDotrahd ⤑ DJcy Ђ DScy Ѕ DZcy Џ Dagger ‡ Darr ↡ Dashv ⫤ Dcaron Ď Dcy Д Del ∇ Delta Δ Dfr 𝔇 DiacriticalAcute ´ DiacriticalDot ˙ DiacriticalDoubleAcute ˝ DiacriticalGrave ` DiacriticalTilde ˜ Diamond ⋄ DifferentialD ⅆ Dopf 𝔻 Dot ¨ DotDot ⃜ DotEqual ≐ DoubleContourIntegral ∯ DoubleDot ¨ DoubleDownArrow ⇓ DoubleLeftArrow ⇐ DoubleLeftRightArrow ⇔ DoubleLeftTee ⫤ DoubleLongLeftArrow ⟸ DoubleLongLeftRightArrow ⟺ DoubleLongRightArrow ⟹ DoubleRightArrow ⇒ DoubleRightTee ⊨ DoubleUpArrow ⇑ DoubleUpDownArrow ⇕ DoubleVerticalBar ∥ DownArrow ↓ DownArrowBar ⤓ DownArrowUpArrow ⇵ DownBreve ̑ DownLeftRightVector ⥐ DownLeftTeeVector ⥞ DownLeftVector ↽ DownLeftVectorBar ⥖ DownRightTeeVector ⥟ DownRightVector ⇁ DownRightVectorBar ⥗ DownTee ⊤ DownTeeArrow ↧ Downarrow ⇓ Dscr 𝒟 Dstrok Đ ENG Ŋ ETH Ð Eacute É Ecaron Ě Ecirc Ê Ecy Э Edot Ė Efr 𝔈 Egrave È Element ∈ Emacr Ē EmptySmallSquare ◻ EmptyVerySmallSquare ▫ Eogon Ę Eopf 𝔼 Epsilon Ε Equal ⩵ EqualTilde ≂ Equilibrium ⇌ Escr ℰ Esim ⩳ Eta Η Euml Ë Exists ∃ ExponentialE ⅇ Fcy Ф Ffr 𝔉 FilledSmallSquare ◼ FilledVerySmallSquare ▪ Fopf 𝔽 ForAll ∀ Fouriertrf ℱ Fscr ℱ GJcy Ѓ GT > Gamma Γ Gammad Ϝ Gbreve Ğ Gcedil Ģ Gcirc Ĝ Gcy Г Gdot Ġ Gfr 𝔊 Gg ⋙ Gopf 𝔾 GreaterEqual ≥ GreaterEqualLess ⋛ GreaterFullEqual ≧ GreaterGreater ⪢ GreaterLess ≷ GreaterSlantEqual ⩾ GreaterTilde ≳ Gscr 𝒢 Gt ≫ HARDcy Ъ Hacek ˇ Hat ^ Hcirc Ĥ Hfr ℌ HilbertSpace ℋ Hopf ℍ HorizontalLine ─ Hscr ℋ Hstrok Ħ HumpDownHump ≎ HumpEqual ≏ IEcy Е IJlig Ĳ IOcy Ё Iacute Í Icirc Î Icy И Idot İ Ifr ℑ Igrave Ì Im ℑ Imacr Ī ImaginaryI ⅈ Implies ⇒ Int ∬ Integral ∫ Intersection ⋂ InvisibleComma ⁣ InvisibleTimes ⁢ Iogon Į Iopf 𝕀 Iota Ι Iscr ℐ Itilde Ĩ Iukcy І Iuml Ï Jcirc Ĵ Jcy Й Jfr 𝔍 Jopf 𝕁 Jscr 𝒥 Jsercy Ј Jukcy Є KHcy Х KJcy Ќ Kappa Κ Kcedil Ķ Kcy К Kfr 𝔎 Kopf 𝕂 Kscr 𝒦 LJcy Љ LT < Lacute Ĺ Lambda Λ Lang ⟪ Laplacetrf ℒ Larr ↞ Lcaron Ľ Lcedil Ļ Lcy Л LeftAngleBracket ⟨ LeftArrow ← LeftArrowBar ⇤ LeftArrowRightArrow ⇆ LeftCeiling ⌈ LeftDoubleBracket ⟦ LeftDownTeeVector ⥡ LeftDownVector ⇃ LeftDownVectorBar ⥙ LeftFloor ⌊ LeftRightArrow ↔ LeftRightVector ⥎ LeftTee ⊣ LeftTeeArrow ↤ LeftTeeVector ⥚ LeftTriangle ⊲ LeftTriangleBar ⧏ LeftTriangleEqual ⊴ LeftUpDownVector ⥑ LeftUpTeeVector ⥠ LeftUpVector ↿ LeftUpVectorBar ⥘ LeftVector ↼ LeftVectorBar ⥒ Leftarrow ⇐ Leftrightarrow ⇔ LessEqualGreater ⋚ LessFullEqual ≦ LessGreater ≶ LessLess ⪡ LessSlantEqual ⩽ LessTilde ≲ Lfr 𝔏 Ll ⋘ Lleftarrow ⇚ Lmidot Ŀ LongLeftArrow ⟵ LongLeftRightArrow ⟷ LongRightArrow ⟶ Longleftarrow ⟸ Longleftrightarrow ⟺ Longrightarrow ⟹ Lopf 𝕃 LowerLeftArrow ↙ LowerRightArrow ↘ Lscr ℒ Lsh ↰ Lstrok Ł Lt ≪ Map ⤅ Mcy М MediumSpace   Mellintrf ℳ Mfr 𝔐 MinusPlus ∓ Mopf 𝕄 Mscr ℳ Mu Μ NJcy Њ Nacute Ń Ncaron Ň Ncedil Ņ Ncy Н NegativeMediumSpace ​ NegativeThickSpace ​ NegativeThinSpace ​ NegativeVeryThinSpace ​ NestedGreaterGreater ≫ NestedLessLess ≪ NewLine \n Nfr 𝔑 NoBreak ⁠ NonBreakingSpace   Nopf ℕ Not ⫬ NotCongruent ≢ NotCupCap ≭ NotDoubleVerticalBar ∦ NotElement ∉ NotEqual ≠ NotEqualTilde ≂̸ NotExists ∄ NotGreater ≯ NotGreaterEqual ≱ NotGreaterFullEqual ≧̸ NotGreaterGreater ≫̸ NotGreaterLess ≹ NotGreaterSlantEqual ⩾̸ NotGreaterTilde ≵ NotHumpDownHump ≎̸ NotHumpEqual ≏̸ NotLeftTriangle ⋪ NotLeftTriangleBar ⧏̸ NotLeftTriangleEqual ⋬ NotLess ≮ NotLessEqual ≰ NotLessGreater ≸ NotLessLess ≪̸ NotLessSlantEqual ⩽̸ NotLessTilde ≴ NotNestedGreaterGreater ⪢̸ NotNestedLessLess ⪡̸ NotPrecedes ⊀ NotPrecedesEqual ⪯̸ NotPrecedesSlantEqual ⋠ NotReverseElement ∌ NotRightTriangle ⋫ NotRightTriangleBar ⧐̸ NotRightTriangleEqual ⋭ NotSquareSubset ⊏̸ NotSquareSubsetEqual ⋢ NotSquareSuperset ⊐̸ NotSquareSupersetEqual ⋣ NotSubset ⊂⃒ NotSubsetEqual ⊈ NotSucceeds ⊁ NotSucceedsEqual ⪰̸ NotSucceedsSlantEqual ⋡ NotSucceedsTilde ≿̸ NotSuperset ⊃⃒ NotSupersetEqual ⊉ NotTilde ≁ NotTildeEqual ≄ NotTildeFullEqual ≇ NotTildeTilde ≉ NotVerticalBar ∤ Nscr 𝒩 Ntilde Ñ Nu Ν OElig Œ Oacute Ó Ocirc Ô Ocy О Odblac Ő Ofr 𝔒 Ograve Ò Omacr Ō Omega Ω Omicron Ο Oopf 𝕆 OpenCurlyDoubleQuote “ OpenCurlyQuote ‘ Or ⩔ Oscr 𝒪 Oslash Ø Otilde Õ Otimes ⨷ Ouml Ö OverBar ‾ OverBrace ⏞ OverBracket ⎴ OverParenthesis ⏜ PartialD ∂ Pcy П Pfr 𝔓 Phi Φ Pi Π PlusMinus ± Poincareplane ℌ Popf ℙ Pr ⪻ Precedes ≺ PrecedesEqual ⪯ PrecedesSlantEqual ≼ PrecedesTilde ≾ Prime ″ Product ∏ Proportion ∷ Proportional ∝ Pscr 𝒫 Psi Ψ QUOT \" Qfr 𝔔 Qopf ℚ Qscr 𝒬 RBarr ⤐ REG ® Racute Ŕ Rang ⟫ Rarr ↠ Rarrtl ⤖ Rcaron Ř Rcedil Ŗ Rcy Р Re ℜ ReverseElement ∋ ReverseEquilibrium ⇋ ReverseUpEquilibrium ⥯ Rfr ℜ Rho Ρ RightAngleBracket ⟩ RightArrow → RightArrowBar ⇥ RightArrowLeftArrow ⇄ RightCeiling ⌉ RightDoubleBracket ⟧ RightDownTeeVector ⥝ RightDownVector ⇂ RightDownVectorBar ⥕ RightFloor ⌋ RightTee ⊢ RightTeeArrow ↦ RightTeeVector ⥛ RightTriangle ⊳ RightTriangleBar ⧐ RightTriangleEqual ⊵ RightUpDownVector ⥏ RightUpTeeVector ⥜ RightUpVector ↾ RightUpVectorBar ⥔ RightVector ⇀ RightVectorBar ⥓ Rightarrow ⇒ Ropf ℝ RoundImplies ⥰ Rrightarrow ⇛ Rscr ℛ Rsh ↱ RuleDelayed ⧴ SHCHcy Щ SHcy Ш SOFTcy Ь Sacute Ś Sc ⪼ Scaron Š Scedil Ş Scirc Ŝ Scy С Sfr 𝔖 ShortDownArrow ↓ ShortLeftArrow ← ShortRightArrow → ShortUpArrow ↑ Sigma Σ SmallCircle ∘ Sopf 𝕊 Sqrt √ Square □ SquareIntersection ⊓ SquareSubset ⊏ SquareSubsetEqual ⊑ SquareSuperset ⊐ SquareSupersetEqual ⊒ SquareUnion ⊔ Sscr 𝒮 Star ⋆ Sub ⋐ Subset ⋐ SubsetEqual ⊆ Succeeds ≻ SucceedsEqual ⪰ SucceedsSlantEqual ≽ SucceedsTilde ≿ SuchThat ∋ Sum ∑ Sup ⋑ Superset ⊃ SupersetEqual ⊇ Supset ⋑ THORN Þ TRADE ™ TSHcy Ћ TScy Ц Tab \t Tau Τ Tcaron Ť Tcedil Ţ Tcy Т Tfr 𝔗 Therefore ∴ Theta Θ ThickSpace    ThinSpace   Tilde ∼ TildeEqual ≃ TildeFullEqual ≅ TildeTilde ≈ Topf 𝕋 TripleDot ⃛ Tscr 𝒯 Tstrok Ŧ Uacute Ú Uarr ↟ Uarrocir ⥉ Ubrcy Ў Ubreve Ŭ Ucirc Û Ucy У Udblac Ű Ufr 𝔘 Ugrave Ù Umacr Ū UnderBar _ UnderBrace ⏟ UnderBracket ⎵ UnderParenthesis ⏝ Union ⋃ UnionPlus ⊎ Uogon Ų Uopf 𝕌 UpArrow ↑ UpArrowBar ⤒ UpArrowDownArrow ⇅ UpDownArrow ↕ UpEquilibrium ⥮ UpTee ⊥ UpTeeArrow ↥ Uparrow ⇑ Updownarrow ⇕ UpperLeftArrow ↖ UpperRightArrow ↗ Upsi ϒ Upsilon Υ Uring Ů Uscr 𝒰 Utilde Ũ Uuml Ü VDash ⊫ Vbar ⫫ Vcy В Vdash ⊩ Vdashl ⫦ Vee ⋁ Verbar ‖ Vert ‖ VerticalBar ∣ VerticalLine | VerticalSeparator ❘ VerticalTilde ≀ VeryThinSpace   Vfr 𝔙 Vopf 𝕍 Vscr 𝒱 Vvdash ⊪ Wcirc Ŵ Wedge ⋀ Wfr 𝔚 Wopf 𝕎 Wscr 𝒲 Xfr 𝔛 Xi Ξ Xopf 𝕏 Xscr 𝒳 YAcy Я YIcy Ї YUcy Ю Yacute Ý Ycirc Ŷ Ycy Ы Yfr 𝔜 Yopf 𝕐 Yscr 𝒴 Yuml Ÿ ZHcy Ж Zacute Ź Zcaron Ž Zcy З Zdot Ż ZeroWidthSpace ​ Zeta Ζ Zfr ℨ Zopf ℤ Zscr 𝒵 aacute á abreve ă ac ∾ acE ∾̳ acd ∿ acirc â acute ´ acy а aelig æ af ⁡ afr 𝔞 agrave à alefsym ℵ aleph ℵ alpha α amacr ā amalg ⨿ amp & and ∧ andand ⩕ andd ⩜ andslope ⩘ andv ⩚ ang ∠ ange ⦤ angle ∠ angmsd ∡ angmsdaa ⦨ angmsdab ⦩ angmsdac ⦪ angmsdad ⦫ angmsdae ⦬ angmsdaf ⦭ angmsdag ⦮ angmsdah ⦯ angrt ∟ angrtvb ⊾ angrtvbd ⦝ angsph ∢ angst Å angzarr ⍼ aogon ą aopf 𝕒 ap ≈ apE ⩰ apacir ⩯ ape ≊ apid ≋ apos ' approx ≈ approxeq ≊ aring å ascr 𝒶 ast * asymp ≈ asympeq ≍ atilde ã auml ä awconint ∳ awint ⨑ bNot ⫭ backcong ≌ backepsilon ϶ backprime ‵ backsim ∽ backsimeq ⋍ barvee ⊽ barwed ⌅ barwedge ⌅ bbrk ⎵ bbrktbrk ⎶ bcong ≌ bcy б bdquo „ becaus ∵ because ∵ bemptyv ⦰ bepsi ϶ bernou ℬ beta β beth ℶ between ≬ bfr 𝔟 bigcap ⋂ bigcirc ◯ bigcup ⋃ bigodot ⨀ bigoplus ⨁ bigotimes ⨂ bigsqcup ⨆ bigstar ★ bigtriangledown ▽ bigtriangleup △ biguplus ⨄ bigvee ⋁ bigwedge ⋀ bkarow ⤍ blacklozenge ⧫ blacksquare ▪ blacktriangle ▴ blacktriangledown ▾ blacktriangleleft ◂ blacktriangleright ▸ blank ␣ blk12 ▒ blk14 ░ blk34 ▓ block █ bne =⃥ bnequiv ≡⃥ bnot ⌐ bopf 𝕓 bot ⊥ bottom ⊥ bowtie ⋈ boxDL ╗ boxDR ╔ boxDl ╖ boxDr ╓ boxH ═ boxHD ╦ boxHU ╩ boxHd ╤ boxHu ╧ boxUL ╝ boxUR ╚ boxUl ╜ boxUr ╙ boxV ║ boxVH ╬ boxVL ╣ boxVR ╠ boxVh ╫ boxVl ╢ boxVr ╟ boxbox ⧉ boxdL ╕ boxdR ╒ boxdl ┐ boxdr ┌ boxh ─ boxhD ╥ boxhU ╨ boxhd ┬ boxhu ┴ boxminus ⊟ boxplus ⊞ boxtimes ⊠ boxuL ╛ boxuR ╘ boxul ┘ boxur └ boxv │ boxvH ╪ boxvL ╡ boxvR ╞ boxvh ┼ boxvl ┤ boxvr ├ bprime ‵ breve ˘ brvbar ¦ bscr 𝒷 bsemi ⁏ bsim ∽ bsime ⋍ bsol \\ bsolb ⧅ bsolhsub ⟈ bull • bullet • bump ≎ bumpE ⪮ bumpe ≏ bumpeq ≏ cacute ć cap ∩ capand ⩄ capbrcup ⩉ capcap ⩋ capcup ⩇ capdot ⩀ caps ∩︀ caret ⁁ caron ˇ ccaps ⩍ ccaron č ccedil ç ccirc ĉ ccups ⩌ ccupssm ⩐ cdot ċ cedil ¸ cemptyv ⦲ cent ¢ centerdot · cfr 𝔠 chcy ч check ✓ checkmark ✓ chi χ cir ○ cirE ⧃ circ ˆ circeq ≗ circlearrowleft ↺ circlearrowright ↻ circledR ® circledS Ⓢ circledast ⊛ circledcirc ⊚ circleddash ⊝ cire ≗ cirfnint ⨐ cirmid ⫯ cirscir ⧂ clubs ♣ clubsuit ♣ colon : colone ≔ coloneq ≔ comma , commat @ comp ∁ compfn ∘ complement ∁ complexes ℂ cong ≅ congdot ⩭ conint ∮ copf 𝕔 coprod ∐ copy © copysr ℗ crarr ↵ cross ✗ cscr 𝒸 csub ⫏ csube ⫑ csup ⫐ csupe ⫒ ctdot ⋯ cudarrl ⤸ cudarrr ⤵ cuepr ⋞ cuesc ⋟ cularr ↶ cularrp ⤽ cup ∪ cupbrcap ⩈ cupcap ⩆ cupcup ⩊ cupdot ⊍ cupor ⩅ cups ∪︀ curarr ↷ curarrm ⤼ curlyeqprec ⋞ curlyeqsucc ⋟ curlyvee ⋎ curlywedge ⋏ curren ¤ curvearrowleft ↶ curvearrowright ↷ cuvee ⋎ cuwed ⋏ cwconint ∲ cwint ∱ cylcty ⌭ dArr ⇓ dHar ⥥ dagger † daleth ℸ darr ↓ dash ‐ dashv ⊣ dbkarow ⤏ dblac ˝ dcaron ď dcy д dd ⅆ ddagger ‡ ddarr ⇊ ddotseq ⩷ deg ° delta δ demptyv ⦱ dfisht ⥿ dfr 𝔡 dharl ⇃ dharr ⇂ diam ⋄ diamond ⋄ diamondsuit ♦ diams ♦ die ¨ digamma ϝ disin ⋲ div ÷ divide ÷ divideontimes ⋇ divonx ⋇ djcy ђ dlcorn ⌞ dlcrop ⌍ dollar $ dopf 𝕕 dot ˙ doteq ≐ doteqdot ≑ dotminus ∸ dotplus ∔ dotsquare ⊡ doublebarwedge ⌆ downarrow ↓ downdownarrows ⇊ downharpoonleft ⇃ downharpoonright ⇂ drbkarow ⤐ drcorn ⌟ drcrop ⌌ dscr 𝒹 dscy ѕ dsol ⧶ dstrok đ dtdot ⋱ dtri ▿ dtrif ▾ duarr ⇵ duhar ⥯ dwangle ⦦ dzcy џ dzigrarr ⟿ eDDot ⩷ eDot ≑ eacute é easter ⩮ ecaron ě ecir ≖ ecirc ê ecolon ≕ ecy э edot ė ee ⅇ efDot ≒ efr 𝔢 eg ⪚ egrave è egs ⪖ egsdot ⪘ el ⪙ elinters ⏧ ell ℓ els ⪕ elsdot ⪗ emacr ē empty ∅ emptyset ∅ emptyv ∅ emsp   emsp13   emsp14   eng ŋ ensp   eogon ę eopf 𝕖 epar ⋕ eparsl ⧣ eplus ⩱ epsi ε epsilon ε epsiv ϵ eqcirc ≖ eqcolon ≕ eqsim ≂ eqslantgtr ⪖ eqslantless ⪕ equals = equest ≟ equiv ≡ equivDD ⩸ eqvparsl ⧥ erDot ≓ erarr ⥱ escr ℯ esdot ≐ esim ≂ eta η eth ð euml ë euro € excl ! exist ∃ expectation ℰ exponentiale ⅇ fallingdotseq ≒ fcy ф female ♀ ffilig ﬃ fflig ﬀ ffllig ﬄ ffr 𝔣 filig ﬁ fjlig fj flat ♭ fllig ﬂ fltns ▱ fnof ƒ fopf 𝕗 forall ∀ fork ⋔ forkv ⫙ fpartint ⨍ frac12 ½ frac13 ⅓ frac14 ¼ frac15 ⅕ frac16 ⅙ frac18 ⅛ frac23 ⅔ frac25 ⅖ frac34 ¾ frac35 ⅗ frac38 ⅜ frac45 ⅘ frac56 ⅚ frac58 ⅝ frac78 ⅞ frasl ⁄ frown ⌢ fscr 𝒻 gE ≧ gEl ⪌ gacute ǵ gamma γ gammad ϝ gap ⪆ gbreve ğ gcirc ĝ gcy г gdot ġ ge ≥ gel ⋛ geq ≥ geqq ≧ geqslant ⩾ ges ⩾ gescc ⪩ gesdot ⪀ gesdoto ⪂ gesdotol ⪄ gesl ⋛︀ gesles ⪔ gfr 𝔤 gg ≫ ggg ⋙ gimel ℷ gjcy ѓ gl ≷ glE ⪒ gla ⪥ glj ⪤ gnE ≩ gnap ⪊ gnapprox ⪊ gne ⪈ gneq ⪈ gneqq ≩ gnsim ⋧ gopf 𝕘 grave ` gscr ℊ gsim ≳ gsime ⪎ gsiml ⪐ gt > gtcc ⪧ gtcir ⩺ gtdot ⋗ gtlPar ⦕ gtquest ⩼ gtrapprox ⪆ gtrarr ⥸ gtrdot ⋗ gtreqless ⋛ gtreqqless ⪌ gtrless ≷ gtrsim ≳ gvertneqq ≩︀ gvnE ≩︀ hArr ⇔ hairsp   half ½ hamilt ℋ hardcy ъ harr ↔ harrcir ⥈ harrw ↭ hbar ℏ hcirc ĥ hearts ♥ heartsuit ♥ hellip … hercon ⊹ hfr 𝔥 hksearow ⤥ hkswarow ⤦ hoarr ⇿ homtht ∻ hookleftarrow ↩ hookrightarrow ↪ hopf 𝕙 horbar ― hscr 𝒽 hslash ℏ hstrok ħ hybull ⁃ hyphen ‐ iacute í ic ⁣ icirc î icy и iecy е iexcl ¡ iff ⇔ ifr 𝔦 igrave ì ii ⅈ iiiint ⨌ iiint ∭ iinfin ⧜ iiota ℩ ijlig ĳ imacr ī image ℑ imagline ℐ imagpart ℑ imath ı imof ⊷ imped Ƶ in ∈ incare ℅ infin ∞ infintie ⧝ inodot ı int ∫ intcal ⊺ integers ℤ intercal ⊺ intlarhk ⨗ intprod ⨼ iocy ё iogon į iopf 𝕚 iota ι iprod ⨼ iquest ¿ iscr 𝒾 isin ∈ isinE ⋹ isindot ⋵ isins ⋴ isinsv ⋳ isinv ∈ it ⁢ itilde ĩ iukcy і iuml ï jcirc ĵ jcy й jfr 𝔧 jmath ȷ jopf 𝕛 jscr 𝒿 jsercy ј jukcy є kappa κ kappav ϰ kcedil ķ kcy к kfr 𝔨 kgreen ĸ khcy х kjcy ќ kopf 𝕜 kscr 𝓀 lAarr ⇚ lArr ⇐ lAtail ⤛ lBarr ⤎ lE ≦ lEg ⪋ lHar ⥢ lacute ĺ laemptyv ⦴ lagran ℒ lambda λ lang ⟨ langd ⦑ langle ⟨ lap ⪅ laquo « larr ← larrb ⇤ larrbfs ⤟ larrfs ⤝ larrhk ↩ larrlp ↫ larrpl ⤹ larrsim ⥳ larrtl ↢ lat ⪫ latail ⤙ late ⪭ lates ⪭︀ lbarr ⤌ lbbrk ❲ lbrace { lbrack [ lbrke ⦋ lbrksld ⦏ lbrkslu ⦍ lcaron ľ lcedil ļ lceil ⌈ lcub { lcy л ldca ⤶ ldquo “ ldquor „ ldrdhar ⥧ ldrushar ⥋ ldsh ↲ le ≤ leftarrow ← leftarrowtail ↢ leftharpoondown ↽ leftharpoonup ↼ leftleftarrows ⇇ leftrightarrow ↔ leftrightarrows ⇆ leftrightharpoons ⇋ leftrightsquigarrow ↭ leftthreetimes ⋋ leg ⋚ leq ≤ leqq ≦ leqslant ⩽ les ⩽ lescc ⪨ lesdot ⩿ lesdoto ⪁ lesdotor ⪃ lesg ⋚︀ lesges ⪓ lessapprox ⪅ lessdot ⋖ lesseqgtr ⋚ lesseqqgtr ⪋ lessgtr ≶ lesssim ≲ lfisht ⥼ lfloor ⌊ lfr 𝔩 lg ≶ lgE ⪑ lhard ↽ lharu ↼ lharul ⥪ lhblk ▄ ljcy љ ll ≪ llarr ⇇ llcorner ⌞ llhard ⥫ lltri ◺ lmidot ŀ lmoust ⎰ lmoustache ⎰ lnE ≨ lnap ⪉ lnapprox ⪉ lne ⪇ lneq ⪇ lneqq ≨ lnsim ⋦ loang ⟬ loarr ⇽ lobrk ⟦ longleftarrow ⟵ longleftrightarrow ⟷ longmapsto ⟼ longrightarrow ⟶ looparrowleft ↫ looparrowright ↬ lopar ⦅ lopf 𝕝 loplus ⨭ lotimes ⨴ lowast ∗ lowbar _ loz ◊ lozenge ◊ lozf ⧫ lpar ( lparlt ⦓ lrarr ⇆ lrcorner ⌟ lrhar ⇋ lrhard ⥭ lrm ‎ lrtri ⊿ lsaquo ‹ lscr 𝓁 lsh ↰ lsim ≲ lsime ⪍ lsimg ⪏ lsqb [ lsquo ‘ lsquor ‚ lstrok ł lt < ltcc ⪦ ltcir ⩹ ltdot ⋖ lthree ⋋ ltimes ⋉ ltlarr ⥶ ltquest ⩻ ltrPar ⦖ ltri ◃ ltrie ⊴ ltrif ◂ lurdshar ⥊ luruhar ⥦ lvertneqq ≨︀ lvnE ≨︀ mDDot ∺ macr ¯ male ♂ malt ✠ maltese ✠ map ↦ mapsto ↦ mapstodown ↧ mapstoleft ↤ mapstoup ↥ marker ▮ mcomma ⨩ mcy м mdash — measuredangle ∡ mfr 𝔪 mho ℧ micro µ mid ∣ midast * midcir ⫰ middot · minus − minusb ⊟ minusd ∸ minusdu ⨪ mlcp ⫛ mldr … mnplus ∓ models ⊧ mopf 𝕞 mp ∓ mscr 𝓂 mstpos ∾ mu μ multimap ⊸ mumap ⊸ nGg ⋙̸ nGt ≫⃒ nGtv ≫̸ nLeftarrow ⇍ nLeftrightarrow ⇎ nLl ⋘̸ nLt ≪⃒ nLtv ≪̸ nRightarrow ⇏ nVDash ⊯ nVdash ⊮ nabla ∇ nacute ń nang ∠⃒ nap ≉ napE ⩰̸ napid ≋̸ napos ŉ napprox ≉ natur ♮ natural ♮ naturals ℕ nbsp   nbump ≎̸ nbumpe ≏̸ ncap ⩃ ncaron ň ncedil ņ ncong ≇ ncongdot ⩭̸ ncup ⩂ ncy н ndash – ne ≠ neArr ⇗ nearhk ⤤ nearr ↗ nearrow ↗ nedot ≐̸ nequiv ≢ nesear ⤨ nesim ≂̸ nexist ∄ nexists ∄ nfr 𝔫 ngE ≧̸ nge ≱ ngeq ≱ ngeqq ≧̸ ngeqslant ⩾̸ nges ⩾̸ ngsim ≵ ngt ≯ ngtr ≯ nhArr ⇎ nharr ↮ nhpar ⫲ ni ∋ nis ⋼ nisd ⋺ niv ∋ njcy њ nlArr ⇍ nlE ≦̸ nlarr ↚ nldr ‥ nle ≰ nleftarrow ↚ nleftrightarrow ↮ nleq ≰ nleqq ≦̸ nleqslant ⩽̸ nles ⩽̸ nless ≮ nlsim ≴ nlt ≮ nltri ⋪ nltrie ⋬ nmid ∤ nopf 𝕟 not ¬ notin ∉ notinE ⋹̸ notindot ⋵̸ notinva ∉ notinvb ⋷ notinvc ⋶ notni ∌ notniva ∌ notnivb ⋾ notnivc ⋽ npar ∦ nparallel ∦ nparsl ⫽⃥ npart ∂̸ npolint ⨔ npr ⊀ nprcue ⋠ npre ⪯̸ nprec ⊀ npreceq ⪯̸ nrArr ⇏ nrarr ↛ nrarrc ⤳̸ nrarrw ↝̸ nrightarrow ↛ nrtri ⋫ nrtrie ⋭ nsc ⊁ nsccue ⋡ nsce ⪰̸ nscr 𝓃 nshortmid ∤ nshortparallel ∦ nsim ≁ nsime ≄ nsimeq ≄ nsmid ∤ nspar ∦ nsqsube ⋢ nsqsupe ⋣ nsub ⊄ nsubE ⫅̸ nsube ⊈ nsubset ⊂⃒ nsubseteq ⊈ nsubseteqq ⫅̸ nsucc ⊁ nsucceq ⪰̸ nsup ⊅ nsupE ⫆̸ nsupe ⊉ nsupset ⊃⃒ nsupseteq ⊉ nsupseteqq ⫆̸ ntgl ≹ ntilde ñ ntlg ≸ ntriangleleft ⋪ ntrianglelefteq ⋬ ntriangleright ⋫ ntrianglerighteq ⋭ nu ν num # numero № numsp   nvDash ⊭ nvHarr ⤄ nvap ≍⃒ nvdash ⊬ nvge ≥⃒ nvgt >⃒ nvinfin ⧞ nvlArr ⤂ nvle ≤⃒ nvlt <⃒ nvltrie ⊴⃒ nvrArr ⤃ nvrtrie ⊵⃒ nvsim ∼⃒ nwArr ⇖ nwarhk ⤣ nwarr ↖ nwarrow ↖ nwnear ⤧ oS Ⓢ oacute ó oast ⊛ ocir ⊚ ocirc ô ocy о odash ⊝ odblac ő odiv ⨸ odot ⊙ odsold ⦼ oelig œ ofcir ⦿ ofr 𝔬 ogon ˛ ograve ò ogt ⧁ ohbar ⦵ ohm Ω oint ∮ olarr ↺ olcir ⦾ olcross ⦻ oline ‾ olt ⧀ omacr ō omega ω omicron ο omid ⦶ ominus ⊖ oopf 𝕠 opar ⦷ operp ⦹ oplus ⊕ or ∨ orarr ↻ ord ⩝ order ℴ orderof ℴ ordf ª ordm º origof ⊶ oror ⩖ orslope ⩗ orv ⩛ oscr ℴ oslash ø osol ⊘ otilde õ otimes ⊗ otimesas ⨶ ouml ö ovbar ⌽ par ∥ para ¶ parallel ∥ parsim ⫳ parsl ⫽ part ∂ pcy п percnt % period . permil ‰ perp ⊥ pertenk ‱ pfr 𝔭 phi φ phiv ϕ phmmat ℳ phone ☎ pi π pitchfork ⋔ piv ϖ planck ℏ planckh ℎ plankv ℏ plus + plusacir ⨣ plusb ⊞ pluscir ⨢ plusdo ∔ plusdu ⨥ pluse ⩲ plusmn ± plussim ⨦ plustwo ⨧ pm ± pointint ⨕ popf 𝕡 pound £ pr ≺ prE ⪳ prap ⪷ prcue ≼ pre ⪯ prec ≺ precapprox ⪷ preccurlyeq ≼ preceq ⪯ precnapprox ⪹ precneqq ⪵ precnsim ⋨ precsim ≾ prime ′ primes ℙ prnE ⪵ prnap ⪹ prnsim ⋨ prod ∏ profalar ⌮ profline ⌒ profsurf ⌓ prop ∝ propto ∝ prsim ≾ prurel ⊰ pscr 𝓅 psi ψ puncsp   qfr 𝔮 qint ⨌ qopf 𝕢 qprime ⁗ qscr 𝓆 quaternions ℍ quatint ⨖ quest \? questeq ≟ quot \" rAarr ⇛ rArr ⇒ rAtail ⤜ rBarr ⤏ rHar ⥤ race ∽̱ racute ŕ radic √ raemptyv ⦳ rang ⟩ rangd ⦒ range ⦥ rangle ⟩ raquo » rarr → rarrap ⥵ rarrb ⇥ rarrbfs ⤠ rarrc ⤳ rarrfs ⤞ rarrhk ↪ rarrlp ↬ rarrpl ⥅ rarrsim ⥴ rarrtl ↣ rarrw ↝ ratail ⤚ ratio ∶ rationals ℚ rbarr ⤍ rbbrk ❳ rbrace } rbrack ] rbrke ⦌ rbrksld ⦎ rbrkslu ⦐ rcaron ř rcedil ŗ rceil ⌉ rcub } rcy р rdca ⤷ rdldhar ⥩ rdquo ” rdquor ” rdsh ↳ real ℜ realine ℛ realpart ℜ reals ℝ rect ▭ reg ® rfisht ⥽ rfloor ⌋ rfr 𝔯 rhard ⇁ rharu ⇀ rharul ⥬ rho ρ rhov ϱ rightarrow → rightarrowtail ↣ rightharpoondown ⇁ rightharpoonup ⇀ rightleftarrows ⇄ rightleftharpoons ⇌ rightrightarrows ⇉ rightsquigarrow ↝ rightthreetimes ⋌ ring ˚ risingdotseq ≓ rlarr ⇄ rlhar ⇌ rlm ‏ rmoust ⎱ rmoustache ⎱ rnmid ⫮ roang ⟭ roarr ⇾ robrk ⟧ ropar ⦆ ropf 𝕣 roplus ⨮ rotimes ⨵ rpar ) rpargt ⦔ rppolint ⨒ rrarr ⇉ rsaquo › rscr 𝓇 rsh ↱ rsqb ] rsquo ’ rsquor ’ rthree ⋌ rtimes ⋊ rtri ▹ rtrie ⊵ rtrif ▸ rtriltri ⧎ ruluhar ⥨ rx ℞ sacute ś sbquo ‚ sc ≻ scE ⪴ scap ⪸ scaron š sccue ≽ sce ⪰ scedil ş scirc ŝ scnE ⪶ scnap ⪺ scnsim ⋩ scpolint ⨓ scsim ≿ scy с sdot ⋅ sdotb ⊡ sdote ⩦ seArr ⇘ searhk ⤥ searr ↘ searrow ↘ sect § semi ; seswar ⤩ setminus ∖ setmn ∖ sext ✶ sfr 𝔰 sfrown ⌢ sharp ♯ shchcy щ shcy ш shortmid ∣ shortparallel ∥ shy ­ sigma σ sigmaf ς sigmav ς sim ∼ simdot ⩪ sime ≃ simeq ≃ simg ⪞ simgE ⪠ siml ⪝ simlE ⪟ simne ≆ simplus ⨤ simrarr ⥲ slarr ← smallsetminus ∖ smashp ⨳ smeparsl ⧤ smid ∣ smile ⌣ smt ⪪ smte ⪬ smtes ⪬︀ softcy ь sol / solb ⧄ solbar ⌿ sopf 𝕤 spades ♠ spadesuit ♠ spar ∥ sqcap ⊓ sqcaps ⊓︀ sqcup ⊔ sqcups ⊔︀ sqsub ⊏ sqsube ⊑ sqsubset ⊏ sqsubseteq ⊑ sqsup ⊐ sqsupe ⊒ sqsupset ⊐ sqsupseteq ⊒ squ □ square □ squarf ▪ squf ▪ srarr → sscr 𝓈 ssetmn ∖ ssmile ⌣ sstarf ⋆ star ☆ starf ★ straightepsilon ϵ straightphi ϕ strns ¯ sub ⊂ subE ⫅ subdot ⪽ sube ⊆ subedot ⫃ submult ⫁ subnE ⫋ subne ⊊ subplus ⪿ subrarr ⥹ subset ⊂ subseteq ⊆ subseteqq ⫅ subsetneq ⊊ subsetneqq ⫋ subsim ⫇ subsub ⫕ subsup ⫓ succ ≻ succapprox ⪸ succcurlyeq ≽ succeq ⪰ succnapprox ⪺ succneqq ⪶ succnsim ⋩ succsim ≿ sum ∑ sung ♪ sup ⊃ sup1 ¹ sup2 ² sup3 ³ supE ⫆ supdot ⪾ supdsub ⫘ supe ⊇ supedot ⫄ suphsol ⟉ suphsub ⫗ suplarr ⥻ supmult ⫂ supnE ⫌ supne ⊋ supplus ⫀ supset ⊃ supseteq ⊇ supseteqq ⫆ supsetneq ⊋ supsetneqq ⫌ supsim ⫈ supsub ⫔ supsup ⫖ swArr ⇙ swarhk ⤦ swarr ↙ swarrow ↙ swnwar ⤪ szlig ß target ⌖ tau τ tbrk ⎴ tcaron ť tcedil ţ tcy т tdot ⃛ telrec ⌕ tfr 𝔱 there4 ∴ therefore ∴ theta θ thetasym ϑ thetav ϑ thickapprox ≈ thicksim ∼ thinsp   thkap ≈ thksim ∼ thorn þ tilde ˜ times × timesb ⊠ timesbar ⨱ timesd ⨰ tint ∭ toea ⤨ top ⊤ topbot ⌶ topcir ⫱ topf 𝕥 topfork ⫚ tosa ⤩ tprime ‴ trade ™ triangle ▵ triangledown ▿ triangleleft ◃ trianglelefteq ⊴ triangleq ≜ triangleright ▹ trianglerighteq ⊵ tridot ◬ trie ≜ triminus ⨺ triplus ⨹ trisb ⧍ tritime ⨻ trpezium ⏢ tscr 𝓉 tscy ц tshcy ћ tstrok ŧ twixt ≬ twoheadleftarrow ↞ twoheadrightarrow ↠ uArr ⇑ uHar ⥣ uacute ú uarr ↑ ubrcy ў ubreve ŭ ucirc û ucy у udarr ⇅ udblac ű udhar ⥮ ufisht ⥾ ufr 𝔲 ugrave ù uharl ↿ uharr ↾ uhblk ▀ ulcorn ⌜ ulcorner ⌜ ulcrop ⌏ ultri ◸ umacr ū uml ¨ uogon ų uopf 𝕦 uparrow ↑ updownarrow ↕ upharpoonleft ↿ upharpoonright ↾ uplus ⊎ upsi υ upsih ϒ upsilon υ upuparrows ⇈ urcorn ⌝ urcorner ⌝ urcrop ⌎ uring ů urtri ◹ uscr 𝓊 utdot ⋰ utilde ũ utri ▵ utrif ▴ uuarr ⇈ uuml ü uwangle ⦧ vArr ⇕ vBar ⫨ vBarv ⫩ vDash ⊨ vangrt ⦜ varepsilon ϵ varkappa ϰ varnothing ∅ varphi ϕ varpi ϖ varpropto ∝ varr ↕ varrho ϱ varsigma ς varsubsetneq ⊊︀ varsubsetneqq ⫋︀ varsupsetneq ⊋︀ varsupsetneqq ⫌︀ vartheta ϑ vartriangleleft ⊲ vartriangleright ⊳ vcy в vdash ⊢ vee ∨ veebar ⊻ veeeq ≚ vellip ⋮ verbar | vert | vfr 𝔳 vltri ⊲ vnsub ⊂⃒ vnsup ⊃⃒ vopf 𝕧 vprop ∝ vrtri ⊳ vscr 𝓋 vsubnE ⫋︀ vsubne ⊊︀ vsupnE ⫌︀ vsupne ⊋︀ vzigzag ⦚ wcirc ŵ wedbar ⩟ wedge ∧ wedgeq ≙ weierp ℘ wfr 𝔴 wopf 𝕨 wp ℘ wr ≀ wreath ≀ wscr 𝓌 xcap ⋂ xcirc ◯ xcup ⋃ xdtri ▽ xfr 𝔵 xhArr ⟺ xharr ⟷ xi ξ xlArr ⟸ xlarr ⟵ xmap ⟼ xnis ⋻ xodot ⨀ xopf 𝕩 xoplus ⨁ xotime ⨂ xrArr ⟹ xrarr ⟶ xscr 𝓍 xsqcup ⨆ xuplus ⨄ xutri △ xvee ⋁ xwedge ⋀ yacute ý yacy я ycirc ŷ ycy ы yen ¥ yfr 𝔶 yicy ї yopf 𝕪 yscr 𝓎 yucy ю yuml ÿ zacute ź zcaron ž zcy з zdot ż zeetrf ℨ zeta ζ zfr 𝔷 zhcy ж zigrarr ⇝ zopf 𝕫 zscr 𝓏 zwj ‍ zwnj ‌"};
static const lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharRefData___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharRefData___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharRefData = (const lean_object*)&l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharRefData___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_space(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_space___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences;
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Html_namedCharacterReference_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_namedCharacterReference_x3f___closed__0;
static lean_once_cell_t l_Lean_Html_namedCharacterReference_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Html_namedCharacterReference_x3f___closed__1;
static lean_once_cell_t l_Lean_Html_namedCharacterReference_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_namedCharacterReference_x3f___closed__2;
static lean_once_cell_t l_Lean_Html_namedCharacterReference_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Html_namedCharacterReference_x3f___closed__3;
static const lean_string_object l_Lean_Html_namedCharacterReference_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Html_namedCharacterReference_x3f___closed__4 = (const lean_object*)&l_Lean_Html_namedCharacterReference_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Html_namedCharacterReference_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_characterReference_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_space(lean_object* v_data_3_, lean_object* v_i_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_string_utf8_at_end(v_data_3_, v_i_4_);
if (v___x_5_ == 0)
{
uint32_t v___x_6_; uint32_t v___x_7_; uint8_t v___x_8_; 
v___x_6_ = lean_string_utf8_get_fast(v_data_3_, v_i_4_);
v___x_7_ = 32;
v___x_8_ = lean_uint32_dec_eq(v___x_6_, v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
v___x_9_ = lean_string_utf8_next_fast(v_data_3_, v_i_4_);
lean_dec(v_i_4_);
v_i_4_ = v___x_9_;
goto _start;
}
else
{
return v_i_4_;
}
}
else
{
return v_i_4_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_space___boxed(lean_object* v_data_11_, lean_object* v_i_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_space(v_data_11_, v_i_12_);
lean_dec_ref(v_data_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_go(lean_object* v_data_14_, lean_object* v_i_15_, lean_object* v_acc_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = lean_string_utf8_at_end(v_data_14_, v_i_15_);
if (v___x_17_ == 0)
{
lean_object* v_nameEnd_18_; lean_object* v_denotationStart_19_; lean_object* v_denotationEnd_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
lean_inc(v_i_15_);
v_nameEnd_18_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_space(v_data_14_, v_i_15_);
v_denotationStart_19_ = lean_string_utf8_next(v_data_14_, v_nameEnd_18_);
lean_inc(v_denotationStart_19_);
v_denotationEnd_20_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_space(v_data_14_, v_denotationStart_19_);
v___x_21_ = lean_string_utf8_next(v_data_14_, v_denotationEnd_20_);
v___x_22_ = lean_string_utf8_extract(v_data_14_, v_i_15_, v_nameEnd_18_);
lean_dec(v_nameEnd_18_);
lean_dec(v_i_15_);
v___x_23_ = lean_string_utf8_extract(v_data_14_, v_denotationStart_19_, v_denotationEnd_20_);
lean_dec(v_denotationEnd_20_);
lean_dec(v_denotationStart_19_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_22_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
v___x_25_ = lean_array_push(v_acc_16_, v___x_24_);
v_i_15_ = v___x_21_;
v_acc_16_ = v___x_25_;
goto _start;
}
else
{
lean_dec(v_i_15_);
return v_acc_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_go___boxed(lean_object* v_data_27_, lean_object* v_i_28_, lean_object* v_acc_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_go(v_data_27_, v_i_28_, v_acc_29_);
lean_dec_ref(v_data_27_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData(lean_object* v_data_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = lean_unsigned_to_nat(2125u);
v___x_34_ = lean_mk_empty_array_with_capacity(v___x_33_);
v___x_35_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData_go(v_data_31_, v___x_32_, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData___boxed(lean_object* v_data_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData(v_data_36_);
lean_dec_ref(v_data_36_);
return v_res_37_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = ((lean_object*)(l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharRefData___closed__0));
v___x_39_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_parseNamedCharRefData(v___x_38_);
return v___x_39_;
}
}
static lean_object* _init_l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences___closed__0, &l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences___closed__0_once, _init_l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences___closed__0);
return v___x_40_;
}
}
uint8_t l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0(lean_object* v_a_41_, lean_object* v_b_42_){
_start:
{
lean_object* v_fst_43_; lean_object* v_fst_44_; uint8_t v___x_45_; 
v_fst_43_ = lean_ctor_get(v_a_41_, 0);
v_fst_44_ = lean_ctor_get(v_b_42_, 0);
v___x_45_ = lean_string_dec_lt(v_fst_43_, v_fst_44_);
return v___x_45_;
}
}
LEAN_EXPORT void l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_41_ = stack[0].m_obj;
lean_object* v_b_42_ = stack[1].m_obj;
uint8_t v_res_46_;
v_res_46_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0(v_a_41_, v_b_42_);
stack->m_num = v_res_46_;
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_a_47_, lean_object* v_b_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0(v_a_47_, v_b_48_);
lean_dec_ref(v_b_48_);
lean_dec_ref(v_a_47_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg(lean_object* v_as_51_, lean_object* v_k_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_m_57_; lean_object* v_a_58_; uint8_t v___x_59_; 
v___x_55_ = lean_nat_add(v_x_53_, v_x_54_);
v___x_56_ = lean_unsigned_to_nat(1u);
v_m_57_ = lean_nat_shiftr(v___x_55_, v___x_56_);
lean_dec(v___x_55_);
v_a_58_ = lean_array_fget_borrowed(v_as_51_, v_m_57_);
v___x_59_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0(v_a_58_, v_k_52_);
if (v___x_59_ == 0)
{
uint8_t v___x_60_; 
lean_dec(v_x_54_);
v___x_60_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0(v_k_52_, v_a_58_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec(v_m_57_);
lean_dec(v_x_53_);
lean_inc(v_a_58_);
v___x_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_61_, 0, v_a_58_);
return v___x_61_;
}
else
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = lean_nat_dec_eq(v_m_57_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_nat_sub(v_m_57_, v___x_56_);
lean_dec(v_m_57_);
v___x_65_ = lean_nat_dec_lt(v___x_64_, v_x_53_);
if (v___x_65_ == 0)
{
v_x_54_ = v___x_64_;
goto _start;
}
else
{
lean_object* v___x_67_; 
lean_dec(v___x_64_);
lean_dec(v_x_53_);
v___x_67_ = lean_box(0);
return v___x_67_;
}
}
else
{
lean_object* v___x_68_; 
lean_dec(v_m_57_);
lean_dec(v_x_53_);
v___x_68_ = lean_box(0);
return v___x_68_;
}
}
}
else
{
lean_object* v___x_69_; uint8_t v___x_70_; 
lean_dec(v_x_53_);
v___x_69_ = lean_nat_add(v_m_57_, v___x_56_);
lean_dec(v_m_57_);
v___x_70_ = lean_nat_dec_le(v___x_69_, v_x_54_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec(v___x_69_);
lean_dec(v_x_54_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
else
{
v_x_53_ = v___x_69_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___boxed(lean_object* v_as_73_, lean_object* v_k_74_, lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg(v_as_73_, v_k_74_, v_x_75_, v_x_76_);
lean_dec_ref(v_k_74_);
lean_dec_ref(v_as_73_);
return v_res_77_;
}
}
static lean_object* _init_l_Lean_Html_namedCharacterReference_x3f___closed__0(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences;
v___x_79_ = lean_array_get_size(v___x_78_);
return v___x_79_;
}
}
static uint8_t _init_l_Lean_Html_namedCharacterReference_x3f___closed__1(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_80_ = lean_obj_once(&l_Lean_Html_namedCharacterReference_x3f___closed__0, &l_Lean_Html_namedCharacterReference_x3f___closed__0_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__0);
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = lean_nat_dec_lt(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Html_namedCharacterReference_x3f___closed__2(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = lean_obj_once(&l_Lean_Html_namedCharacterReference_x3f___closed__0, &l_Lean_Html_namedCharacterReference_x3f___closed__0_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__0);
v___x_85_ = lean_nat_sub(v___x_84_, v___x_83_);
return v___x_85_;
}
}
static uint8_t _init_l_Lean_Html_namedCharacterReference_x3f___closed__3(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_86_ = lean_obj_once(&l_Lean_Html_namedCharacterReference_x3f___closed__2, &l_Lean_Html_namedCharacterReference_x3f___closed__2_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__2);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_nat_dec_le(v___x_87_, v___x_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_namedCharacterReference_x3f(lean_object* v_ref_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_91_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences;
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_uint8_once(&l_Lean_Html_namedCharacterReference_x3f___closed__1, &l_Lean_Html_namedCharacterReference_x3f___closed__1_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__1);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec_ref(v_ref_90_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_obj_once(&l_Lean_Html_namedCharacterReference_x3f___closed__2, &l_Lean_Html_namedCharacterReference_x3f___closed__2_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__2);
v___x_96_ = lean_uint8_once(&l_Lean_Html_namedCharacterReference_x3f___closed__3, &l_Lean_Html_namedCharacterReference_x3f___closed__3_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__3);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v_ref_90_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = ((lean_object*)(l_Lean_Html_namedCharacterReference_x3f___closed__4));
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v_ref_90_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg(v___x_91_, v___x_99_, v___x_92_, v___x_95_);
lean_dec_ref_known(v___x_99_, 2);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_box(0);
return v___x_101_;
}
else
{
lean_object* v_val_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_110_; 
v_val_102_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_110_ == 0)
{
v___x_104_ = v___x_100_;
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_val_102_);
lean_dec(v___x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_snd_106_; lean_object* v___x_108_; 
v_snd_106_ = lean_ctor_get(v_val_102_, 1);
lean_inc(v_snd_106_);
lean_dec(v_val_102_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v_snd_106_);
v___x_108_ = v___x_104_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_snd_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0(lean_object* v_as_111_, lean_object* v_k_112_, lean_object* v_x_113_, lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg(v_as_111_, v_k_112_, v_x_113_, v_x_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___boxed(lean_object* v_as_117_, lean_object* v_k_118_, lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0(v_as_117_, v_k_118_, v_x_119_, v_x_120_, v_x_121_);
lean_dec_ref(v_k_118_);
lean_dec_ref(v_as_117_);
return v_res_122_;
}
}
lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f(uint32_t v_c_123_){
_start:
{
uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_148_ = 48;
v___x_149_ = lean_uint32_dec_le(v___x_148_, v_c_123_);
if (v___x_149_ == 0)
{
goto v___jp_137_;
}
else
{
uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 57;
v___x_151_ = lean_uint32_dec_le(v_c_123_, v___x_150_);
if (v___x_151_ == 0)
{
goto v___jp_137_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_152_ = lean_uint32_to_nat(v_c_123_);
v___x_153_ = lean_unsigned_to_nat(48u);
v___x_154_ = lean_nat_sub(v___x_152_, v___x_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
v___jp_124_:
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 65;
v___x_126_ = lean_uint32_dec_le(v___x_125_, v_c_123_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_box(0);
return v___x_127_;
}
else
{
uint32_t v___x_128_; uint8_t v___x_129_; 
v___x_128_ = 70;
v___x_129_ = lean_uint32_dec_le(v_c_123_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
v___x_130_ = lean_box(0);
return v___x_130_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_131_ = lean_unsigned_to_nat(10u);
v___x_132_ = lean_uint32_to_nat(v_c_123_);
v___x_133_ = lean_nat_add(v___x_131_, v___x_132_);
lean_dec(v___x_132_);
v___x_134_ = lean_unsigned_to_nat(65u);
v___x_135_ = lean_nat_sub(v___x_133_, v___x_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
}
v___jp_137_:
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 97;
v___x_139_ = lean_uint32_dec_le(v___x_138_, v_c_123_);
if (v___x_139_ == 0)
{
goto v___jp_124_;
}
else
{
uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = 102;
v___x_141_ = lean_uint32_dec_le(v_c_123_, v___x_140_);
if (v___x_141_ == 0)
{
goto v___jp_124_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_142_ = lean_unsigned_to_nat(10u);
v___x_143_ = lean_uint32_to_nat(v_c_123_);
v___x_144_ = lean_nat_add(v___x_142_, v___x_143_);
lean_dec(v___x_143_);
v___x_145_ = lean_unsigned_to_nat(97u);
v___x_146_ = lean_nat_sub(v___x_144_, v___x_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_123_ = stack[0].m_num;
lean_object* v_res_156_;
v_res_156_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f(v_c_123_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f___boxed(lean_object* v_c_157_){
_start:
{
uint32_t v_c_boxed_158_; lean_object* v_res_159_; 
v_c_boxed_158_ = lean_unbox_uint32(v_c_157_);
lean_dec(v_c_157_);
v_res_159_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f(v_c_boxed_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg(lean_object* v_ref_160_, lean_object* v_radix_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_fst_163_; lean_object* v_snd_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_189_; 
v_fst_163_ = lean_ctor_get(v_a_162_, 0);
v_snd_164_ = lean_ctor_get(v_a_162_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_a_162_);
if (v_isSharedCheck_189_ == 0)
{
v___x_166_ = v_a_162_;
v_isShared_167_ = v_isSharedCheck_189_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_snd_164_);
lean_inc(v_fst_163_);
lean_dec(v_a_162_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_189_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
uint8_t v___x_168_; 
v___x_168_ = lean_string_utf8_at_end(v_ref_160_, v_snd_164_);
if (v___x_168_ == 0)
{
uint32_t v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_string_utf8_get_fast(v_ref_160_, v_snd_164_);
v___x_170_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f(v___x_169_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v___x_171_; 
lean_del_object(v___x_166_);
lean_dec(v_snd_164_);
lean_dec(v_fst_163_);
v___x_171_ = lean_box(0);
return v___x_171_;
}
else
{
lean_object* v_val_172_; uint8_t v___x_173_; 
v_val_172_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_val_172_);
lean_dec_ref_known(v___x_170_, 1);
v___x_173_ = lean_nat_dec_le(v_radix_161_, v_val_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_174_ = lean_nat_mul(v_fst_163_, v_radix_161_);
lean_dec(v_fst_163_);
v___x_175_ = lean_nat_add(v___x_174_, v_val_172_);
lean_dec(v_val_172_);
lean_dec(v___x_174_);
v___x_176_ = lean_unsigned_to_nat(1114111u);
v___x_177_ = lean_nat_dec_lt(v___x_176_, v___x_175_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_string_utf8_next_fast(v_ref_160_, v_snd_164_);
lean_dec(v_snd_164_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_178_);
lean_ctor_set(v___x_166_, 0, v___x_175_);
v___x_180_ = v___x_166_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_182_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
v_a_162_ = v___x_180_;
goto _start;
}
}
else
{
lean_object* v___x_183_; 
lean_dec(v___x_175_);
lean_del_object(v___x_166_);
lean_dec(v_snd_164_);
v___x_183_ = lean_box(0);
return v___x_183_;
}
}
else
{
lean_object* v___x_184_; 
lean_dec(v_val_172_);
lean_del_object(v___x_166_);
lean_dec(v_snd_164_);
lean_dec(v_fst_163_);
v___x_184_ = lean_box(0);
return v___x_184_;
}
}
}
else
{
lean_object* v___x_186_; 
if (v_isShared_167_ == 0)
{
v___x_186_ = v___x_166_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_fst_163_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_snd_164_);
v___x_186_ = v_reuseFailAlloc_188_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; 
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg___boxed(lean_object* v_ref_190_, lean_object* v_radix_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg(v_ref_190_, v_radix_191_, v_a_192_);
lean_dec(v_radix_191_);
lean_dec_ref(v_ref_190_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric(lean_object* v_radix_194_, lean_object* v_ref_195_, lean_object* v_i_196_){
_start:
{
lean_object* v_n_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_n_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v_n_197_);
lean_ctor_set(v___x_198_, 1, v_i_196_);
v___x_199_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg(v_ref_195_, v_radix_194_, v___x_198_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_226_; 
v_val_201_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_226_ == 0)
{
v___x_203_ = v___x_199_;
v_isShared_204_ = v_isSharedCheck_226_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_val_201_);
lean_dec(v___x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_226_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_fst_205_; uint32_t v___x_206_; uint8_t v___y_214_; uint32_t v___x_216_; uint8_t v___x_217_; 
v_fst_205_ = lean_ctor_get(v_val_201_, 0);
lean_inc(v_fst_205_);
lean_dec(v_val_201_);
v___x_206_ = l_Char_ofNat(v_fst_205_);
lean_dec(v_fst_205_);
v___x_216_ = 0;
v___x_217_ = lean_uint32_dec_eq(v___x_206_, v___x_216_);
if (v___x_217_ == 0)
{
uint32_t v___x_218_; uint8_t v___x_219_; 
v___x_218_ = 13;
v___x_219_ = lean_uint32_dec_eq(v___x_206_, v___x_218_);
if (v___x_219_ == 0)
{
uint8_t v___x_220_; 
v___x_220_ = l_Lean_Html_isNonCharacter(v___x_206_);
if (v___x_220_ == 0)
{
uint8_t v___x_221_; 
v___x_221_ = l_Lean_Html_isControl(v___x_206_);
if (v___x_221_ == 0)
{
v___y_214_ = v___x_221_;
goto v___jp_213_;
}
else
{
uint8_t v___x_222_; 
v___x_222_ = l_Lean_Html_isAsciiWhitespace(v___x_206_);
if (v___x_222_ == 0)
{
v___y_214_ = v___x_221_;
goto v___jp_213_;
}
else
{
goto v___jp_207_;
}
}
}
else
{
lean_object* v___x_223_; 
lean_del_object(v___x_203_);
v___x_223_ = lean_box(0);
return v___x_223_;
}
}
else
{
lean_object* v___x_224_; 
lean_del_object(v___x_203_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
}
else
{
lean_object* v___x_225_; 
lean_del_object(v___x_203_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
v___jp_207_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_208_ = ((lean_object*)(l_Lean_Html_namedCharacterReference_x3f___closed__4));
v___x_209_ = lean_string_push(v___x_208_, v___x_206_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_209_);
v___x_211_ = v___x_203_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
v___jp_213_:
{
if (v___y_214_ == 0)
{
goto v___jp_207_;
}
else
{
lean_object* v___x_215_; 
lean_del_object(v___x_203_);
v___x_215_ = lean_box(0);
return v___x_215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric___boxed(lean_object* v_radix_227_, lean_object* v_ref_228_, lean_object* v_i_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric(v_radix_227_, v_ref_228_, v_i_229_);
lean_dec_ref(v_ref_228_);
lean_dec(v_radix_227_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0(lean_object* v_ref_231_, lean_object* v_radix_232_, lean_object* v_inst_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg(v_ref_231_, v_radix_232_, v_a_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___boxed(lean_object* v_ref_236_, lean_object* v_radix_237_, lean_object* v_inst_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0(v_ref_236_, v_radix_237_, v_inst_238_, v_a_239_);
lean_dec(v_radix_237_);
lean_dec_ref(v_ref_236_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_characterReference_x3f(lean_object* v_ref_241_){
_start:
{
lean_object* v_i_242_; uint8_t v___x_243_; 
v_i_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_string_utf8_at_end(v_ref_241_, v_i_242_);
if (v___x_243_ == 0)
{
uint32_t v___x_244_; uint32_t v___x_245_; uint8_t v___x_246_; 
v___x_244_ = lean_string_utf8_get_fast(v_ref_241_, v_i_242_);
v___x_245_ = 35;
v___x_246_ = lean_uint32_dec_eq(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Html_namedCharacterReference_x3f(v_ref_241_);
return v___x_247_;
}
else
{
lean_object* v_i_248_; uint8_t v___x_253_; 
v_i_248_ = lean_string_utf8_next_fast(v_ref_241_, v_i_242_);
v___x_253_ = lean_string_utf8_at_end(v_ref_241_, v_i_248_);
if (v___x_253_ == 0)
{
uint32_t v___x_254_; uint32_t v___x_255_; uint8_t v___x_256_; 
v___x_254_ = lean_string_utf8_get_fast(v_ref_241_, v_i_248_);
v___x_255_ = 120;
v___x_256_ = lean_uint32_dec_eq(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
uint32_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = 88;
v___x_258_ = lean_uint32_dec_eq(v___x_254_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(10u);
v___x_260_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric(v___x_259_, v_ref_241_, v_i_248_);
lean_dec_ref(v_ref_241_);
return v___x_260_;
}
else
{
goto v___jp_249_;
}
}
else
{
goto v___jp_249_;
}
}
else
{
lean_object* v___x_261_; 
lean_dec_ref(v_ref_241_);
v___x_261_ = lean_box(0);
return v___x_261_;
}
v___jp_249_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_unsigned_to_nat(16u);
v___x_251_ = lean_string_utf8_next_fast(v_ref_241_, v_i_248_);
v___x_252_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric(v___x_250_, v_ref_241_, v___x_251_);
lean_dec_ref(v_ref_241_);
return v___x_252_;
}
}
}
else
{
lean_object* v___x_262_; 
lean_dec_ref(v_ref_241_);
v___x_262_ = lean_box(0);
return v___x_262_;
}
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_BinSearch(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Html_Spec(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Html_CharRef(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_BinSearch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences = _init_l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences();
lean_mark_persistent(l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Html_CharRef(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Array_BinSearch(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Html_Spec(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Html_CharRef(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_BinSearch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Html_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_CharRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Html_CharRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Html_CharRef(builtin);
}
#ifdef __cplusplus
}
#endif
