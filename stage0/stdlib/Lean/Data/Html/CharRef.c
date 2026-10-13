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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0(lean_object* v_a_41_, lean_object* v_b_42_){
_start:
{
lean_object* v_fst_43_; lean_object* v_fst_44_; uint8_t v___x_45_; 
v_fst_43_ = lean_ctor_get(v_a_41_, 0);
v_fst_44_ = lean_ctor_get(v_b_42_, 0);
v___x_45_ = lean_string_dec_lt(v_fst_43_, v_fst_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_a_46_, lean_object* v_b_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0(v_a_46_, v_b_47_);
lean_dec_ref(v_b_47_);
lean_dec_ref(v_a_46_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg(lean_object* v_as_50_, lean_object* v_k_51_, lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v_m_56_; lean_object* v_a_57_; uint8_t v___x_58_; 
v___x_54_ = lean_nat_add(v_x_52_, v_x_53_);
v___x_55_ = lean_unsigned_to_nat(1u);
v_m_56_ = lean_nat_shiftr(v___x_54_, v___x_55_);
lean_dec(v___x_54_);
v_a_57_ = lean_array_fget_borrowed(v_as_50_, v_m_56_);
v___x_58_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0(v_a_57_, v_k_51_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; 
lean_dec(v_x_53_);
v___x_59_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___lam__0(v_k_51_, v_a_57_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec(v_m_56_);
lean_dec(v_x_52_);
lean_inc(v_a_57_);
v___x_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_60_, 0, v_a_57_);
return v___x_60_;
}
else
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_nat_dec_eq(v_m_56_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = lean_nat_sub(v_m_56_, v___x_55_);
lean_dec(v_m_56_);
v___x_64_ = lean_nat_dec_lt(v___x_63_, v_x_52_);
if (v___x_64_ == 0)
{
v_x_53_ = v___x_63_;
goto _start;
}
else
{
lean_object* v___x_66_; 
lean_dec(v___x_63_);
lean_dec(v_x_52_);
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
else
{
lean_object* v___x_67_; 
lean_dec(v_m_56_);
lean_dec(v_x_52_);
v___x_67_ = lean_box(0);
return v___x_67_;
}
}
}
else
{
lean_object* v___x_68_; uint8_t v___x_69_; 
lean_dec(v_x_52_);
v___x_68_ = lean_nat_add(v_m_56_, v___x_55_);
lean_dec(v_m_56_);
v___x_69_ = lean_nat_dec_le(v___x_68_, v_x_53_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; 
lean_dec(v___x_68_);
lean_dec(v_x_53_);
v___x_70_ = lean_box(0);
return v___x_70_;
}
else
{
v_x_52_ = v___x_68_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg___boxed(lean_object* v_as_72_, lean_object* v_k_73_, lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg(v_as_72_, v_k_73_, v_x_74_, v_x_75_);
lean_dec_ref(v_k_73_);
lean_dec_ref(v_as_72_);
return v_res_76_;
}
}
static lean_object* _init_l_Lean_Html_namedCharacterReference_x3f___closed__0(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences;
v___x_78_ = lean_array_get_size(v___x_77_);
return v___x_78_;
}
}
static uint8_t _init_l_Lean_Html_namedCharacterReference_x3f___closed__1(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_79_ = lean_obj_once(&l_Lean_Html_namedCharacterReference_x3f___closed__0, &l_Lean_Html_namedCharacterReference_x3f___closed__0_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__0);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_nat_dec_lt(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Html_namedCharacterReference_x3f___closed__2(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_obj_once(&l_Lean_Html_namedCharacterReference_x3f___closed__0, &l_Lean_Html_namedCharacterReference_x3f___closed__0_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__0);
v___x_84_ = lean_nat_sub(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static uint8_t _init_l_Lean_Html_namedCharacterReference_x3f___closed__3(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_85_ = lean_obj_once(&l_Lean_Html_namedCharacterReference_x3f___closed__2, &l_Lean_Html_namedCharacterReference_x3f___closed__2_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__2);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_nat_dec_le(v___x_86_, v___x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_namedCharacterReference_x3f(lean_object* v_ref_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_90_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_namedCharacterReferences;
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_uint8_once(&l_Lean_Html_namedCharacterReference_x3f___closed__1, &l_Lean_Html_namedCharacterReference_x3f___closed__1_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__1);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec_ref(v_ref_89_);
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = lean_obj_once(&l_Lean_Html_namedCharacterReference_x3f___closed__2, &l_Lean_Html_namedCharacterReference_x3f___closed__2_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__2);
v___x_95_ = lean_uint8_once(&l_Lean_Html_namedCharacterReference_x3f___closed__3, &l_Lean_Html_namedCharacterReference_x3f___closed__3_once, _init_l_Lean_Html_namedCharacterReference_x3f___closed__3);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec_ref(v_ref_89_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = ((lean_object*)(l_Lean_Html_namedCharacterReference_x3f___closed__4));
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v_ref_89_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg(v___x_90_, v___x_98_, v___x_91_, v___x_94_);
lean_dec_ref_known(v___x_98_, 2);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
lean_object* v_val_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_109_; 
v_val_101_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_109_ == 0)
{
v___x_103_ = v___x_99_;
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_val_101_);
lean_dec(v___x_99_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v_snd_105_; lean_object* v___x_107_; 
v_snd_105_ = lean_ctor_get(v_val_101_, 1);
lean_inc(v_snd_105_);
lean_dec(v_val_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v_snd_105_);
v___x_107_ = v___x_103_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_snd_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0(lean_object* v_as_110_, lean_object* v_k_111_, lean_object* v_x_112_, lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___redArg(v_as_110_, v_k_111_, v_x_112_, v_x_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0___boxed(lean_object* v_as_116_, lean_object* v_k_117_, lean_object* v_x_118_, lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Array_binSearchAux___at___00Lean_Html_namedCharacterReference_x3f_spec__0(v_as_116_, v_k_117_, v_x_118_, v_x_119_, v_x_120_);
lean_dec_ref(v_k_117_);
lean_dec_ref(v_as_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f(uint32_t v_c_122_){
_start:
{
uint32_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = 48;
v___x_148_ = lean_uint32_dec_le(v___x_147_, v_c_122_);
if (v___x_148_ == 0)
{
goto v___jp_136_;
}
else
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 57;
v___x_150_ = lean_uint32_dec_le(v_c_122_, v___x_149_);
if (v___x_150_ == 0)
{
goto v___jp_136_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_151_ = lean_uint32_to_nat(v_c_122_);
v___x_152_ = lean_unsigned_to_nat(48u);
v___x_153_ = lean_nat_sub(v___x_151_, v___x_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
v___jp_123_:
{
uint32_t v___x_124_; uint8_t v___x_125_; 
v___x_124_ = 65;
v___x_125_ = lean_uint32_dec_le(v___x_124_, v_c_122_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
else
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 70;
v___x_128_ = lean_uint32_dec_le(v_c_122_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_130_ = lean_unsigned_to_nat(10u);
v___x_131_ = lean_uint32_to_nat(v_c_122_);
v___x_132_ = lean_nat_add(v___x_130_, v___x_131_);
lean_dec(v___x_131_);
v___x_133_ = lean_unsigned_to_nat(65u);
v___x_134_ = lean_nat_sub(v___x_132_, v___x_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
}
v___jp_136_:
{
uint32_t v___x_137_; uint8_t v___x_138_; 
v___x_137_ = 97;
v___x_138_ = lean_uint32_dec_le(v___x_137_, v_c_122_);
if (v___x_138_ == 0)
{
goto v___jp_123_;
}
else
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 102;
v___x_140_ = lean_uint32_dec_le(v_c_122_, v___x_139_);
if (v___x_140_ == 0)
{
goto v___jp_123_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_141_ = lean_unsigned_to_nat(10u);
v___x_142_ = lean_uint32_to_nat(v_c_122_);
v___x_143_ = lean_nat_add(v___x_141_, v___x_142_);
lean_dec(v___x_142_);
v___x_144_ = lean_unsigned_to_nat(97u);
v___x_145_ = lean_nat_sub(v___x_143_, v___x_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f___boxed(lean_object* v_c_155_){
_start:
{
uint32_t v_c_boxed_156_; lean_object* v_res_157_; 
v_c_boxed_156_ = lean_unbox_uint32(v_c_155_);
lean_dec(v_c_155_);
v_res_157_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f(v_c_boxed_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg(lean_object* v_ref_158_, lean_object* v_radix_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_187_; 
v_fst_161_ = lean_ctor_get(v_a_160_, 0);
v_snd_162_ = lean_ctor_get(v_a_160_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_a_160_);
if (v_isSharedCheck_187_ == 0)
{
v___x_164_ = v_a_160_;
v_isShared_165_ = v_isSharedCheck_187_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_snd_162_);
lean_inc(v_fst_161_);
lean_dec(v_a_160_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_187_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
uint8_t v___x_166_; 
v___x_166_ = lean_string_utf8_at_end(v_ref_158_, v_snd_162_);
if (v___x_166_ == 0)
{
uint32_t v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_string_utf8_get_fast(v_ref_158_, v_snd_162_);
v___x_168_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_digit_x3f(v___x_167_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v___x_169_; 
lean_del_object(v___x_164_);
lean_dec(v_snd_162_);
lean_dec(v_fst_161_);
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v_val_170_; uint8_t v___x_171_; 
v_val_170_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_val_170_);
lean_dec_ref_known(v___x_168_, 1);
v___x_171_ = lean_nat_dec_le(v_radix_159_, v_val_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_172_ = lean_nat_mul(v_fst_161_, v_radix_159_);
lean_dec(v_fst_161_);
v___x_173_ = lean_nat_add(v___x_172_, v_val_170_);
lean_dec(v_val_170_);
lean_dec(v___x_172_);
v___x_174_ = lean_unsigned_to_nat(1114111u);
v___x_175_ = lean_nat_dec_lt(v___x_174_, v___x_173_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_176_ = lean_string_utf8_next_fast(v_ref_158_, v_snd_162_);
lean_dec(v_snd_162_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v___x_176_);
lean_ctor_set(v___x_164_, 0, v___x_173_);
v___x_178_ = v___x_164_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_176_);
v___x_178_ = v_reuseFailAlloc_180_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
v_a_160_ = v___x_178_;
goto _start;
}
}
else
{
lean_object* v___x_181_; 
lean_dec(v___x_173_);
lean_del_object(v___x_164_);
lean_dec(v_snd_162_);
v___x_181_ = lean_box(0);
return v___x_181_;
}
}
else
{
lean_object* v___x_182_; 
lean_dec(v_val_170_);
lean_del_object(v___x_164_);
lean_dec(v_snd_162_);
lean_dec(v_fst_161_);
v___x_182_ = lean_box(0);
return v___x_182_;
}
}
}
else
{
lean_object* v___x_184_; 
if (v_isShared_165_ == 0)
{
v___x_184_ = v___x_164_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_fst_161_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_snd_162_);
v___x_184_ = v_reuseFailAlloc_186_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg___boxed(lean_object* v_ref_188_, lean_object* v_radix_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg(v_ref_188_, v_radix_189_, v_a_190_);
lean_dec(v_radix_189_);
lean_dec_ref(v_ref_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric(lean_object* v_radix_192_, lean_object* v_ref_193_, lean_object* v_i_194_){
_start:
{
lean_object* v_n_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_n_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v_n_195_);
lean_ctor_set(v___x_196_, 1, v_i_194_);
v___x_197_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg(v_ref_193_, v_radix_192_, v___x_196_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v_val_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_224_; 
v_val_199_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_224_ == 0)
{
v___x_201_ = v___x_197_;
v_isShared_202_ = v_isSharedCheck_224_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_val_199_);
lean_dec(v___x_197_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_224_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v_fst_203_; uint32_t v___x_204_; uint8_t v___y_212_; uint32_t v___x_214_; uint8_t v___x_215_; 
v_fst_203_ = lean_ctor_get(v_val_199_, 0);
lean_inc(v_fst_203_);
lean_dec(v_val_199_);
v___x_204_ = l_Char_ofNat(v_fst_203_);
lean_dec(v_fst_203_);
v___x_214_ = 0;
v___x_215_ = lean_uint32_dec_eq(v___x_204_, v___x_214_);
if (v___x_215_ == 0)
{
uint32_t v___x_216_; uint8_t v___x_217_; 
v___x_216_ = 13;
v___x_217_ = lean_uint32_dec_eq(v___x_204_, v___x_216_);
if (v___x_217_ == 0)
{
uint8_t v___x_218_; 
v___x_218_ = l_Lean_Html_isNonCharacter(v___x_204_);
if (v___x_218_ == 0)
{
uint8_t v___x_219_; 
v___x_219_ = l_Lean_Html_isControl(v___x_204_);
if (v___x_219_ == 0)
{
v___y_212_ = v___x_219_;
goto v___jp_211_;
}
else
{
uint8_t v___x_220_; 
v___x_220_ = l_Lean_Html_isAsciiWhitespace(v___x_204_);
if (v___x_220_ == 0)
{
v___y_212_ = v___x_219_;
goto v___jp_211_;
}
else
{
goto v___jp_205_;
}
}
}
else
{
lean_object* v___x_221_; 
lean_del_object(v___x_201_);
v___x_221_ = lean_box(0);
return v___x_221_;
}
}
else
{
lean_object* v___x_222_; 
lean_del_object(v___x_201_);
v___x_222_ = lean_box(0);
return v___x_222_;
}
}
else
{
lean_object* v___x_223_; 
lean_del_object(v___x_201_);
v___x_223_ = lean_box(0);
return v___x_223_;
}
v___jp_205_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_206_ = ((lean_object*)(l_Lean_Html_namedCharacterReference_x3f___closed__4));
v___x_207_ = lean_string_push(v___x_206_, v___x_204_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_207_);
v___x_209_ = v___x_201_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
v___jp_211_:
{
if (v___y_212_ == 0)
{
goto v___jp_205_;
}
else
{
lean_object* v___x_213_; 
lean_del_object(v___x_201_);
v___x_213_ = lean_box(0);
return v___x_213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric___boxed(lean_object* v_radix_225_, lean_object* v_ref_226_, lean_object* v_i_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric(v_radix_225_, v_ref_226_, v_i_227_);
lean_dec_ref(v_ref_226_);
lean_dec(v_radix_225_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0(lean_object* v_ref_229_, lean_object* v_radix_230_, lean_object* v_inst_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___redArg(v_ref_229_, v_radix_230_, v_a_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0___boxed(lean_object* v_ref_234_, lean_object* v_radix_235_, lean_object* v_inst_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric_spec__0(v_ref_234_, v_radix_235_, v_inst_236_, v_a_237_);
lean_dec(v_radix_235_);
lean_dec_ref(v_ref_234_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_characterReference_x3f(lean_object* v_ref_239_){
_start:
{
lean_object* v_i_240_; uint8_t v___x_241_; 
v_i_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_string_utf8_at_end(v_ref_239_, v_i_240_);
if (v___x_241_ == 0)
{
uint32_t v___x_242_; uint32_t v___x_243_; uint8_t v___x_244_; 
v___x_242_ = lean_string_utf8_get_fast(v_ref_239_, v_i_240_);
v___x_243_ = 35;
v___x_244_ = lean_uint32_dec_eq(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Html_namedCharacterReference_x3f(v_ref_239_);
return v___x_245_;
}
else
{
lean_object* v_i_246_; uint8_t v___x_251_; 
v_i_246_ = lean_string_utf8_next_fast(v_ref_239_, v_i_240_);
v___x_251_ = lean_string_utf8_at_end(v_ref_239_, v_i_246_);
if (v___x_251_ == 0)
{
uint32_t v___x_252_; uint32_t v___x_253_; uint8_t v___x_254_; 
v___x_252_ = lean_string_utf8_get_fast(v_ref_239_, v_i_246_);
v___x_253_ = 120;
v___x_254_ = lean_uint32_dec_eq(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
uint32_t v___x_255_; uint8_t v___x_256_; 
v___x_255_ = 88;
v___x_256_ = lean_uint32_dec_eq(v___x_252_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(10u);
v___x_258_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric(v___x_257_, v_ref_239_, v_i_246_);
lean_dec_ref(v_ref_239_);
return v___x_258_;
}
else
{
goto v___jp_247_;
}
}
else
{
goto v___jp_247_;
}
}
else
{
lean_object* v___x_259_; 
lean_dec_ref(v_ref_239_);
v___x_259_ = lean_box(0);
return v___x_259_;
}
v___jp_247_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_unsigned_to_nat(16u);
v___x_249_ = lean_string_utf8_next_fast(v_ref_239_, v_i_246_);
v___x_250_ = l___private_Lean_Data_Html_CharRef_0__Lean_Html_characterReference_x3f_numeric(v___x_248_, v_ref_239_, v___x_249_);
lean_dec_ref(v_ref_239_);
return v___x_250_;
}
}
}
else
{
lean_object* v___x_260_; 
lean_dec_ref(v_ref_239_);
v___x_260_ = lean_box(0);
return v___x_260_;
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
