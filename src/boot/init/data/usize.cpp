// Lean compiler output
// Module: init.data.usize
// Imports: init.data.uint init.platform init.data.fin.default
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s3_nat_s3_pow_s6___main(obj*, obj*);
obj* _l_s5_usize_s7_to__nat_s7___boxed(obj*);
obj* _l_s5_usize_s13_decidable__eq;
obj* _l_s5_usize_s18_has__decidable__le_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s7_dec__lt_s6___main(size_t, size_t);
obj* _l_s5_usize_s8_has__mod;
obj* _l_s5_usize_s7_dec__eq_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s18_has__decidable__le(size_t, size_t);
obj* _l_s5_usize_s4_modn_s6___main(size_t, obj*);
obj* _l_s5_usize_s3_mul_s6___main(size_t, size_t);
obj* _l_s3_fin_s3_sub_s6___main(obj*, obj*, obj*);
obj* _l_s5_usize_s2_le_s6___main;
obj* _l_s5_usize_s3_sub_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s3_add_s6___main_s7___boxed(obj*, obj*);
obj* _l_s3_fin_s3_add_s6___main(obj*, obj*, obj*);
obj* _l_s5_usize_s3_div_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s4_modn(size_t, obj*);
obj* _l_s5_usize_s9_has__zero;
obj* _l_s5_usize_s3_div_s6___main(size_t, size_t);
obj* _l_s5_usize_s7_dec__lt(size_t, size_t);
obj* _l_s5_usize_s4_modn_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s3_add(size_t, size_t);
obj* _l_s5_usize_s3_mod_s6___main_s7___boxed(obj*, obj*);
obj* _l_s3_fin_s3_div_s6___main(obj*, obj*, obj*);
obj* _l_s5_usize_s4_modn_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s2_lt_s6___main;
obj* _l_s5_usize_s3_mod_s7___boxed(obj*, obj*);
obj* _l_s6_system_s8_platform_s5_nbits;
obj* _l_s5_usize_s3_mul(size_t, size_t);
obj* _l_s5_usize_s18_has__decidable__lt(size_t, size_t);
obj* _l_s5_usize_s8_has__mul;
obj* _l_s5_usize_s3_add_s6___main(size_t, size_t);
obj* _l_s3_fin_s7_of__nat(obj*, obj*);
obj* _l_s5_usize_s3_mod_s6___main(size_t, size_t);
obj* _l_s5_usize_s3_add_s7___boxed(obj*, obj*);
obj* _l_s3_fin_s4_modn_s6___main(obj*, obj*, obj*);
obj* _l_s3_fin_s3_mul_s6___main(obj*, obj*, obj*);
obj* _l_s5_usize_s8_has__add;
obj* _l_s5_usize_s3_mul_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s9_has__modn;
obj* _l_s5_usize_s2_lt;
obj* _l_s5_usize_s7_has__le;
obj* _l_s5_usize_s8_has__div;
obj* _l_s5_usize_s7_of__nat_s11___closed__1;
obj* _l_s5_usize_s3_sub_s6___main(size_t, size_t);
obj* _l_s5_usize_s7_has__lt;
obj* _l_s5_usize_s7_dec__eq_s6___main(size_t, size_t);
obj* _l_s5_usize_s7_dec__le_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s7_dec__eq_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s7_to__nat_s6___main_s7___boxed(obj*);
obj* _l_s5_usize_s3_sub_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s3_div_s6___main_s7___boxed(obj*, obj*);
obj* _l_s9_usize__sz;
obj* _l_s5_usize_s8_has__sub;
obj* _l_s5_usize_s2_le;
obj* _l_s3_fin_s3_mod_s6___main(obj*, obj*, obj*);
obj* _l_s5_usize_s8_has__one;
obj* _l_s5_usize_s7_dec__lt_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s7_dec__le_s6___main(size_t, size_t);
obj* _l_s5_usize_s3_sub(size_t, size_t);
obj* _l_s5_usize_s7_dec__le_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s7_of__nat(obj*);
obj* _l_s5_usize_s3_mod(size_t, size_t);
obj* _l_s5_usize_s7_dec__eq(size_t, size_t);
obj* _l_s5_usize_s7_to__nat_s6___main(size_t);
obj* _l_s5_usize_s7_to__nat(size_t);
obj* _l_s5_usize_s9_inhabited;
obj* _l_s5_usize_s18_has__decidable__lt_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s7_dec__le(size_t, size_t);
obj* _l_s5_usize_s3_mul_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s3_div(size_t, size_t);
obj* _l_s5_usize_s7_dec__lt_s7___boxed(obj*, obj*);
obj* _init__l_s9_usize__sz() {
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::mk_nat_obj(2u);
x_1 = _l_s6_system_s8_platform_s5_nbits;
lean::inc(x_1);
x_3 = _l_s3_nat_s3_pow_s6___main(x_0, x_1);
return x_3;
}
}
obj* _l_s5_usize_s7_of__nat(obj* x_0) {
{
obj* x_1; obj* x_3; obj* x_4; 
x_1 = _l_s5_usize_s7_of__nat_s11___closed__1;
lean::inc(x_1);
x_3 = _l_s3_fin_s7_of__nat(x_1, x_0);
x_4 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init__l_s5_usize_s7_of__nat_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_112; obj* x_114; obj* x_115; obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; obj* x_127; obj* x_129; obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_139; obj* x_140; obj* x_142; obj* x_144; obj* x_145; obj* x_147; obj* x_149; obj* x_150; obj* x_152; obj* x_154; obj* x_155; obj* x_157; obj* x_159; obj* x_160; obj* x_162; obj* x_164; obj* x_165; obj* x_167; obj* x_169; obj* x_170; obj* x_172; obj* x_174; obj* x_175; obj* x_177; obj* x_179; obj* x_180; obj* x_182; obj* x_184; obj* x_185; obj* x_187; obj* x_189; obj* x_190; obj* x_192; obj* x_194; obj* x_195; obj* x_197; obj* x_199; obj* x_200; obj* x_202; obj* x_204; obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_215; obj* x_217; obj* x_219; obj* x_220; obj* x_222; obj* x_224; obj* x_225; obj* x_227; obj* x_229; obj* x_230; obj* x_232; obj* x_234; obj* x_235; obj* x_237; obj* x_239; obj* x_240; obj* x_242; obj* x_244; obj* x_245; obj* x_247; obj* x_249; obj* x_250; obj* x_252; obj* x_254; obj* x_255; obj* x_257; obj* x_259; obj* x_260; obj* x_262; obj* x_264; obj* x_265; obj* x_267; obj* x_269; obj* x_270; obj* x_272; obj* x_274; obj* x_275; obj* x_277; obj* x_279; obj* x_280; obj* x_282; obj* x_284; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_292; obj* x_294; obj* x_295; obj* x_297; obj* x_299; obj* x_300; obj* x_302; obj* x_304; obj* x_305; obj* x_309; obj* x_310; obj* x_314; obj* x_315; obj* x_317; obj* x_319; obj* x_320; obj* x_323; obj* x_326; obj* x_329; obj* x_332; obj* x_335; obj* x_338; obj* x_341; obj* x_344; obj* x_347; obj* x_350; obj* x_353; obj* x_356; obj* x_359; obj* x_362; obj* x_365; obj* x_368; obj* x_371; obj* x_374; obj* x_377; obj* x_380; obj* x_383; obj* x_386; obj* x_389; obj* x_392; obj* x_395; obj* x_398; obj* x_401; obj* x_404; obj* x_407; obj* x_410; obj* x_413; obj* x_416; obj* x_419; obj* x_422; obj* x_425; obj* x_428; obj* x_431; obj* x_434; obj* x_437; obj* x_440; obj* x_443; obj* x_446; obj* x_449; obj* x_452; obj* x_455; obj* x_458; obj* x_461; obj* x_464; obj* x_467; obj* x_470; obj* x_473; obj* x_476; obj* x_479; obj* x_482; obj* x_485; obj* x_488; obj* x_491; obj* x_494; obj* x_497; obj* x_500; obj* x_503; obj* x_506; obj* x_509; obj* x_512; 
x_0 = lean::mk_nat_obj(2u);
x_1 = lean::mk_nat_obj(63u);
lean::inc(x_0);
x_3 = _l_s3_nat_s3_pow_s6___main(x_0, x_1);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_mul(x_3, x_4);
lean::dec(x_3);
x_7 = lean::mk_nat_obj(62u);
lean::inc(x_0);
x_9 = _l_s3_nat_s3_pow_s6___main(x_0, x_7);
x_10 = lean::nat_mul(x_9, x_4);
lean::dec(x_9);
x_12 = lean::mk_nat_obj(61u);
lean::inc(x_0);
x_14 = _l_s3_nat_s3_pow_s6___main(x_0, x_12);
x_15 = lean::nat_mul(x_14, x_4);
lean::dec(x_14);
x_17 = lean::mk_nat_obj(60u);
lean::inc(x_0);
x_19 = _l_s3_nat_s3_pow_s6___main(x_0, x_17);
x_20 = lean::nat_mul(x_19, x_4);
lean::dec(x_19);
x_22 = lean::mk_nat_obj(59u);
lean::inc(x_0);
x_24 = _l_s3_nat_s3_pow_s6___main(x_0, x_22);
x_25 = lean::nat_mul(x_24, x_4);
lean::dec(x_24);
x_27 = lean::mk_nat_obj(58u);
lean::inc(x_0);
x_29 = _l_s3_nat_s3_pow_s6___main(x_0, x_27);
x_30 = lean::nat_mul(x_29, x_4);
lean::dec(x_29);
x_32 = lean::mk_nat_obj(57u);
lean::inc(x_0);
x_34 = _l_s3_nat_s3_pow_s6___main(x_0, x_32);
x_35 = lean::nat_mul(x_34, x_4);
lean::dec(x_34);
x_37 = lean::mk_nat_obj(56u);
lean::inc(x_0);
x_39 = _l_s3_nat_s3_pow_s6___main(x_0, x_37);
x_40 = lean::nat_mul(x_39, x_4);
lean::dec(x_39);
x_42 = lean::mk_nat_obj(55u);
lean::inc(x_0);
x_44 = _l_s3_nat_s3_pow_s6___main(x_0, x_42);
x_45 = lean::nat_mul(x_44, x_4);
lean::dec(x_44);
x_47 = lean::mk_nat_obj(54u);
lean::inc(x_0);
x_49 = _l_s3_nat_s3_pow_s6___main(x_0, x_47);
x_50 = lean::nat_mul(x_49, x_4);
lean::dec(x_49);
x_52 = lean::mk_nat_obj(53u);
lean::inc(x_0);
x_54 = _l_s3_nat_s3_pow_s6___main(x_0, x_52);
x_55 = lean::nat_mul(x_54, x_4);
lean::dec(x_54);
x_57 = lean::mk_nat_obj(52u);
lean::inc(x_0);
x_59 = _l_s3_nat_s3_pow_s6___main(x_0, x_57);
x_60 = lean::nat_mul(x_59, x_4);
lean::dec(x_59);
x_62 = lean::mk_nat_obj(51u);
lean::inc(x_0);
x_64 = _l_s3_nat_s3_pow_s6___main(x_0, x_62);
x_65 = lean::nat_mul(x_64, x_4);
lean::dec(x_64);
x_67 = lean::mk_nat_obj(50u);
lean::inc(x_0);
x_69 = _l_s3_nat_s3_pow_s6___main(x_0, x_67);
x_70 = lean::nat_mul(x_69, x_4);
lean::dec(x_69);
x_72 = lean::mk_nat_obj(49u);
lean::inc(x_0);
x_74 = _l_s3_nat_s3_pow_s6___main(x_0, x_72);
x_75 = lean::nat_mul(x_74, x_4);
lean::dec(x_74);
x_77 = lean::mk_nat_obj(48u);
lean::inc(x_0);
x_79 = _l_s3_nat_s3_pow_s6___main(x_0, x_77);
x_80 = lean::nat_mul(x_79, x_4);
lean::dec(x_79);
x_82 = lean::mk_nat_obj(47u);
lean::inc(x_0);
x_84 = _l_s3_nat_s3_pow_s6___main(x_0, x_82);
x_85 = lean::nat_mul(x_84, x_4);
lean::dec(x_84);
x_87 = lean::mk_nat_obj(46u);
lean::inc(x_0);
x_89 = _l_s3_nat_s3_pow_s6___main(x_0, x_87);
x_90 = lean::nat_mul(x_89, x_4);
lean::dec(x_89);
x_92 = lean::mk_nat_obj(45u);
lean::inc(x_0);
x_94 = _l_s3_nat_s3_pow_s6___main(x_0, x_92);
x_95 = lean::nat_mul(x_94, x_4);
lean::dec(x_94);
x_97 = lean::mk_nat_obj(44u);
lean::inc(x_0);
x_99 = _l_s3_nat_s3_pow_s6___main(x_0, x_97);
x_100 = lean::nat_mul(x_99, x_4);
lean::dec(x_99);
x_102 = lean::mk_nat_obj(43u);
lean::inc(x_0);
x_104 = _l_s3_nat_s3_pow_s6___main(x_0, x_102);
x_105 = lean::nat_mul(x_104, x_4);
lean::dec(x_104);
x_107 = lean::mk_nat_obj(42u);
lean::inc(x_0);
x_109 = _l_s3_nat_s3_pow_s6___main(x_0, x_107);
x_110 = lean::nat_mul(x_109, x_4);
lean::dec(x_109);
x_112 = lean::mk_nat_obj(41u);
lean::inc(x_0);
x_114 = _l_s3_nat_s3_pow_s6___main(x_0, x_112);
x_115 = lean::nat_mul(x_114, x_4);
lean::dec(x_114);
x_117 = lean::mk_nat_obj(40u);
lean::inc(x_0);
x_119 = _l_s3_nat_s3_pow_s6___main(x_0, x_117);
x_120 = lean::nat_mul(x_119, x_4);
lean::dec(x_119);
x_122 = lean::mk_nat_obj(39u);
lean::inc(x_0);
x_124 = _l_s3_nat_s3_pow_s6___main(x_0, x_122);
x_125 = lean::nat_mul(x_124, x_4);
lean::dec(x_124);
x_127 = lean::mk_nat_obj(38u);
lean::inc(x_0);
x_129 = _l_s3_nat_s3_pow_s6___main(x_0, x_127);
x_130 = lean::nat_mul(x_129, x_4);
lean::dec(x_129);
x_132 = lean::mk_nat_obj(37u);
lean::inc(x_0);
x_134 = _l_s3_nat_s3_pow_s6___main(x_0, x_132);
x_135 = lean::nat_mul(x_134, x_4);
lean::dec(x_134);
x_137 = lean::mk_nat_obj(36u);
lean::inc(x_0);
x_139 = _l_s3_nat_s3_pow_s6___main(x_0, x_137);
x_140 = lean::nat_mul(x_139, x_4);
lean::dec(x_139);
x_142 = lean::mk_nat_obj(35u);
lean::inc(x_0);
x_144 = _l_s3_nat_s3_pow_s6___main(x_0, x_142);
x_145 = lean::nat_mul(x_144, x_4);
lean::dec(x_144);
x_147 = lean::mk_nat_obj(34u);
lean::inc(x_0);
x_149 = _l_s3_nat_s3_pow_s6___main(x_0, x_147);
x_150 = lean::nat_mul(x_149, x_4);
lean::dec(x_149);
x_152 = lean::mk_nat_obj(33u);
lean::inc(x_0);
x_154 = _l_s3_nat_s3_pow_s6___main(x_0, x_152);
x_155 = lean::nat_mul(x_154, x_4);
lean::dec(x_154);
x_157 = lean::mk_nat_obj(32u);
lean::inc(x_0);
x_159 = _l_s3_nat_s3_pow_s6___main(x_0, x_157);
x_160 = lean::nat_mul(x_159, x_4);
lean::dec(x_159);
x_162 = lean::mk_nat_obj(31u);
lean::inc(x_0);
x_164 = _l_s3_nat_s3_pow_s6___main(x_0, x_162);
x_165 = lean::nat_mul(x_164, x_4);
lean::dec(x_164);
x_167 = lean::mk_nat_obj(30u);
lean::inc(x_0);
x_169 = _l_s3_nat_s3_pow_s6___main(x_0, x_167);
x_170 = lean::nat_mul(x_169, x_4);
lean::dec(x_169);
x_172 = lean::mk_nat_obj(29u);
lean::inc(x_0);
x_174 = _l_s3_nat_s3_pow_s6___main(x_0, x_172);
x_175 = lean::nat_mul(x_174, x_4);
lean::dec(x_174);
x_177 = lean::mk_nat_obj(28u);
lean::inc(x_0);
x_179 = _l_s3_nat_s3_pow_s6___main(x_0, x_177);
x_180 = lean::nat_mul(x_179, x_4);
lean::dec(x_179);
x_182 = lean::mk_nat_obj(27u);
lean::inc(x_0);
x_184 = _l_s3_nat_s3_pow_s6___main(x_0, x_182);
x_185 = lean::nat_mul(x_184, x_4);
lean::dec(x_184);
x_187 = lean::mk_nat_obj(26u);
lean::inc(x_0);
x_189 = _l_s3_nat_s3_pow_s6___main(x_0, x_187);
x_190 = lean::nat_mul(x_189, x_4);
lean::dec(x_189);
x_192 = lean::mk_nat_obj(25u);
lean::inc(x_0);
x_194 = _l_s3_nat_s3_pow_s6___main(x_0, x_192);
x_195 = lean::nat_mul(x_194, x_4);
lean::dec(x_194);
x_197 = lean::mk_nat_obj(24u);
lean::inc(x_0);
x_199 = _l_s3_nat_s3_pow_s6___main(x_0, x_197);
x_200 = lean::nat_mul(x_199, x_4);
lean::dec(x_199);
x_202 = lean::mk_nat_obj(23u);
lean::inc(x_0);
x_204 = _l_s3_nat_s3_pow_s6___main(x_0, x_202);
x_205 = lean::nat_mul(x_204, x_4);
lean::dec(x_204);
x_207 = lean::mk_nat_obj(22u);
lean::inc(x_0);
x_209 = _l_s3_nat_s3_pow_s6___main(x_0, x_207);
x_210 = lean::nat_mul(x_209, x_4);
lean::dec(x_209);
x_212 = lean::mk_nat_obj(21u);
lean::inc(x_0);
x_214 = _l_s3_nat_s3_pow_s6___main(x_0, x_212);
x_215 = lean::nat_mul(x_214, x_4);
lean::dec(x_214);
x_217 = lean::mk_nat_obj(20u);
lean::inc(x_0);
x_219 = _l_s3_nat_s3_pow_s6___main(x_0, x_217);
x_220 = lean::nat_mul(x_219, x_4);
lean::dec(x_219);
x_222 = lean::mk_nat_obj(19u);
lean::inc(x_0);
x_224 = _l_s3_nat_s3_pow_s6___main(x_0, x_222);
x_225 = lean::nat_mul(x_224, x_4);
lean::dec(x_224);
x_227 = lean::mk_nat_obj(18u);
lean::inc(x_0);
x_229 = _l_s3_nat_s3_pow_s6___main(x_0, x_227);
x_230 = lean::nat_mul(x_229, x_4);
lean::dec(x_229);
x_232 = lean::mk_nat_obj(17u);
lean::inc(x_0);
x_234 = _l_s3_nat_s3_pow_s6___main(x_0, x_232);
x_235 = lean::nat_mul(x_234, x_4);
lean::dec(x_234);
x_237 = lean::mk_nat_obj(16u);
lean::inc(x_0);
x_239 = _l_s3_nat_s3_pow_s6___main(x_0, x_237);
x_240 = lean::nat_mul(x_239, x_4);
lean::dec(x_239);
x_242 = lean::mk_nat_obj(15u);
lean::inc(x_0);
x_244 = _l_s3_nat_s3_pow_s6___main(x_0, x_242);
x_245 = lean::nat_mul(x_244, x_4);
lean::dec(x_244);
x_247 = lean::mk_nat_obj(14u);
lean::inc(x_0);
x_249 = _l_s3_nat_s3_pow_s6___main(x_0, x_247);
x_250 = lean::nat_mul(x_249, x_4);
lean::dec(x_249);
x_252 = lean::mk_nat_obj(13u);
lean::inc(x_0);
x_254 = _l_s3_nat_s3_pow_s6___main(x_0, x_252);
x_255 = lean::nat_mul(x_254, x_4);
lean::dec(x_254);
x_257 = lean::mk_nat_obj(12u);
lean::inc(x_0);
x_259 = _l_s3_nat_s3_pow_s6___main(x_0, x_257);
x_260 = lean::nat_mul(x_259, x_4);
lean::dec(x_259);
x_262 = lean::mk_nat_obj(11u);
lean::inc(x_0);
x_264 = _l_s3_nat_s3_pow_s6___main(x_0, x_262);
x_265 = lean::nat_mul(x_264, x_4);
lean::dec(x_264);
x_267 = lean::mk_nat_obj(10u);
lean::inc(x_0);
x_269 = _l_s3_nat_s3_pow_s6___main(x_0, x_267);
x_270 = lean::nat_mul(x_269, x_4);
lean::dec(x_269);
x_272 = lean::mk_nat_obj(9u);
lean::inc(x_0);
x_274 = _l_s3_nat_s3_pow_s6___main(x_0, x_272);
x_275 = lean::nat_mul(x_274, x_4);
lean::dec(x_274);
x_277 = lean::mk_nat_obj(8u);
lean::inc(x_0);
x_279 = _l_s3_nat_s3_pow_s6___main(x_0, x_277);
x_280 = lean::nat_mul(x_279, x_4);
lean::dec(x_279);
x_282 = lean::mk_nat_obj(7u);
lean::inc(x_0);
x_284 = _l_s3_nat_s3_pow_s6___main(x_0, x_282);
x_285 = lean::nat_mul(x_284, x_4);
lean::dec(x_284);
x_287 = lean::mk_nat_obj(6u);
lean::inc(x_0);
x_289 = _l_s3_nat_s3_pow_s6___main(x_0, x_287);
x_290 = lean::nat_mul(x_289, x_4);
lean::dec(x_289);
x_292 = lean::mk_nat_obj(5u);
lean::inc(x_0);
x_294 = _l_s3_nat_s3_pow_s6___main(x_0, x_292);
x_295 = lean::nat_mul(x_294, x_4);
lean::dec(x_294);
x_297 = lean::mk_nat_obj(4u);
lean::inc(x_0);
x_299 = _l_s3_nat_s3_pow_s6___main(x_0, x_297);
x_300 = lean::nat_mul(x_299, x_4);
lean::dec(x_299);
x_302 = lean::mk_nat_obj(3u);
lean::inc(x_0);
x_304 = _l_s3_nat_s3_pow_s6___main(x_0, x_302);
x_305 = lean::nat_mul(x_304, x_4);
lean::dec(x_304);
lean::inc(x_0);
lean::inc(x_0);
x_309 = _l_s3_nat_s3_pow_s6___main(x_0, x_0);
x_310 = lean::nat_mul(x_309, x_4);
lean::dec(x_309);
lean::inc(x_4);
lean::inc(x_0);
x_314 = _l_s3_nat_s3_pow_s6___main(x_0, x_4);
x_315 = lean::nat_mul(x_314, x_4);
lean::dec(x_314);
x_317 = lean::mk_nat_obj(0u);
lean::inc(x_317);
x_319 = _l_s3_nat_s3_pow_s6___main(x_0, x_317);
x_320 = lean::nat_mul(x_319, x_4);
lean::dec(x_4);
lean::dec(x_319);
x_323 = lean::nat_add(x_320, x_317);
lean::dec(x_317);
lean::dec(x_320);
x_326 = lean::nat_add(x_315, x_323);
lean::dec(x_323);
lean::dec(x_315);
x_329 = lean::nat_add(x_310, x_326);
lean::dec(x_326);
lean::dec(x_310);
x_332 = lean::nat_add(x_305, x_329);
lean::dec(x_329);
lean::dec(x_305);
x_335 = lean::nat_add(x_300, x_332);
lean::dec(x_332);
lean::dec(x_300);
x_338 = lean::nat_add(x_295, x_335);
lean::dec(x_335);
lean::dec(x_295);
x_341 = lean::nat_add(x_290, x_338);
lean::dec(x_338);
lean::dec(x_290);
x_344 = lean::nat_add(x_285, x_341);
lean::dec(x_341);
lean::dec(x_285);
x_347 = lean::nat_add(x_280, x_344);
lean::dec(x_344);
lean::dec(x_280);
x_350 = lean::nat_add(x_275, x_347);
lean::dec(x_347);
lean::dec(x_275);
x_353 = lean::nat_add(x_270, x_350);
lean::dec(x_350);
lean::dec(x_270);
x_356 = lean::nat_add(x_265, x_353);
lean::dec(x_353);
lean::dec(x_265);
x_359 = lean::nat_add(x_260, x_356);
lean::dec(x_356);
lean::dec(x_260);
x_362 = lean::nat_add(x_255, x_359);
lean::dec(x_359);
lean::dec(x_255);
x_365 = lean::nat_add(x_250, x_362);
lean::dec(x_362);
lean::dec(x_250);
x_368 = lean::nat_add(x_245, x_365);
lean::dec(x_365);
lean::dec(x_245);
x_371 = lean::nat_add(x_240, x_368);
lean::dec(x_368);
lean::dec(x_240);
x_374 = lean::nat_add(x_235, x_371);
lean::dec(x_371);
lean::dec(x_235);
x_377 = lean::nat_add(x_230, x_374);
lean::dec(x_374);
lean::dec(x_230);
x_380 = lean::nat_add(x_225, x_377);
lean::dec(x_377);
lean::dec(x_225);
x_383 = lean::nat_add(x_220, x_380);
lean::dec(x_380);
lean::dec(x_220);
x_386 = lean::nat_add(x_215, x_383);
lean::dec(x_383);
lean::dec(x_215);
x_389 = lean::nat_add(x_210, x_386);
lean::dec(x_386);
lean::dec(x_210);
x_392 = lean::nat_add(x_205, x_389);
lean::dec(x_389);
lean::dec(x_205);
x_395 = lean::nat_add(x_200, x_392);
lean::dec(x_392);
lean::dec(x_200);
x_398 = lean::nat_add(x_195, x_395);
lean::dec(x_395);
lean::dec(x_195);
x_401 = lean::nat_add(x_190, x_398);
lean::dec(x_398);
lean::dec(x_190);
x_404 = lean::nat_add(x_185, x_401);
lean::dec(x_401);
lean::dec(x_185);
x_407 = lean::nat_add(x_180, x_404);
lean::dec(x_404);
lean::dec(x_180);
x_410 = lean::nat_add(x_175, x_407);
lean::dec(x_407);
lean::dec(x_175);
x_413 = lean::nat_add(x_170, x_410);
lean::dec(x_410);
lean::dec(x_170);
x_416 = lean::nat_add(x_165, x_413);
lean::dec(x_413);
lean::dec(x_165);
x_419 = lean::nat_add(x_160, x_416);
lean::dec(x_416);
lean::dec(x_160);
x_422 = lean::nat_add(x_155, x_419);
lean::dec(x_419);
lean::dec(x_155);
x_425 = lean::nat_add(x_150, x_422);
lean::dec(x_422);
lean::dec(x_150);
x_428 = lean::nat_add(x_145, x_425);
lean::dec(x_425);
lean::dec(x_145);
x_431 = lean::nat_add(x_140, x_428);
lean::dec(x_428);
lean::dec(x_140);
x_434 = lean::nat_add(x_135, x_431);
lean::dec(x_431);
lean::dec(x_135);
x_437 = lean::nat_add(x_130, x_434);
lean::dec(x_434);
lean::dec(x_130);
x_440 = lean::nat_add(x_125, x_437);
lean::dec(x_437);
lean::dec(x_125);
x_443 = lean::nat_add(x_120, x_440);
lean::dec(x_440);
lean::dec(x_120);
x_446 = lean::nat_add(x_115, x_443);
lean::dec(x_443);
lean::dec(x_115);
x_449 = lean::nat_add(x_110, x_446);
lean::dec(x_446);
lean::dec(x_110);
x_452 = lean::nat_add(x_105, x_449);
lean::dec(x_449);
lean::dec(x_105);
x_455 = lean::nat_add(x_100, x_452);
lean::dec(x_452);
lean::dec(x_100);
x_458 = lean::nat_add(x_95, x_455);
lean::dec(x_455);
lean::dec(x_95);
x_461 = lean::nat_add(x_90, x_458);
lean::dec(x_458);
lean::dec(x_90);
x_464 = lean::nat_add(x_85, x_461);
lean::dec(x_461);
lean::dec(x_85);
x_467 = lean::nat_add(x_80, x_464);
lean::dec(x_464);
lean::dec(x_80);
x_470 = lean::nat_add(x_75, x_467);
lean::dec(x_467);
lean::dec(x_75);
x_473 = lean::nat_add(x_70, x_470);
lean::dec(x_470);
lean::dec(x_70);
x_476 = lean::nat_add(x_65, x_473);
lean::dec(x_473);
lean::dec(x_65);
x_479 = lean::nat_add(x_60, x_476);
lean::dec(x_476);
lean::dec(x_60);
x_482 = lean::nat_add(x_55, x_479);
lean::dec(x_479);
lean::dec(x_55);
x_485 = lean::nat_add(x_50, x_482);
lean::dec(x_482);
lean::dec(x_50);
x_488 = lean::nat_add(x_45, x_485);
lean::dec(x_485);
lean::dec(x_45);
x_491 = lean::nat_add(x_40, x_488);
lean::dec(x_488);
lean::dec(x_40);
x_494 = lean::nat_add(x_35, x_491);
lean::dec(x_491);
lean::dec(x_35);
x_497 = lean::nat_add(x_30, x_494);
lean::dec(x_494);
lean::dec(x_30);
x_500 = lean::nat_add(x_25, x_497);
lean::dec(x_497);
lean::dec(x_25);
x_503 = lean::nat_add(x_20, x_500);
lean::dec(x_500);
lean::dec(x_20);
x_506 = lean::nat_add(x_15, x_503);
lean::dec(x_503);
lean::dec(x_15);
x_509 = lean::nat_add(x_10, x_506);
lean::dec(x_506);
lean::dec(x_10);
x_512 = lean::nat_add(x_5, x_509);
lean::dec(x_509);
lean::dec(x_5);
return x_512;
}
}
obj* _l_s5_usize_s7_to__nat_s6___main(size_t x_0) {
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s5_usize_s7_to__nat_s6___main_s7___boxed(obj* x_0) {
{
size_t x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = _l_s5_usize_s7_to__nat_s6___main(x_1);
return x_2;
}
}
obj* _l_s5_usize_s7_to__nat(size_t x_0) {
{
obj* x_1; 
x_1 = _l_s5_usize_s7_to__nat_s6___main(x_0);
return x_1;
}
}
obj* _l_s5_usize_s7_to__nat_s7___boxed(obj* x_0) {
{
size_t x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = _l_s5_usize_s7_to__nat(x_1);
return x_2;
}
}
obj* _l_s5_usize_s3_add_s6___main(size_t x_0, size_t x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s9_usize__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_add_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s5_usize_s3_add_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s3_add_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s3_add(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = _l_s5_usize_s3_add_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s3_add_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s3_add(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s3_sub_s6___main(size_t x_0, size_t x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s9_usize__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_sub_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s5_usize_s3_sub_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s3_sub_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s3_sub(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = _l_s5_usize_s3_sub_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s3_sub_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s3_sub(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s3_mul_s6___main(size_t x_0, size_t x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s9_usize__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_mul_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s5_usize_s3_mul_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s3_mul_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s3_mul(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = _l_s5_usize_s3_mul_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s3_mul_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s3_mul(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s3_div_s6___main(size_t x_0, size_t x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s9_usize__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_div_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s5_usize_s3_div_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s3_div_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s3_div(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = _l_s5_usize_s3_div_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s3_div_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s3_div(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s3_mod_s6___main(size_t x_0, size_t x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s9_usize__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_mod_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s5_usize_s3_mod_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s3_mod_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s3_mod(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = _l_s5_usize_s3_mod_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s3_mod_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s3_mod(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s4_modn_s6___main(size_t x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = _l_s9_usize__sz;
lean::inc(x_5);
x_7 = _l_s3_fin_s4_modn_s6___main(x_5, x_2, x_1);
if (lean::is_scalar(x_4)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_4;
}
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _l_s5_usize_s4_modn_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; obj* x_3; 
x_2 = lean::unbox_size_t(x_0);
x_3 = _l_s5_usize_s4_modn_s6___main(x_2, x_1);
return x_3;
}
}
obj* _l_s5_usize_s4_modn(size_t x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s5_usize_s4_modn_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s4_modn_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; obj* x_3; 
x_2 = lean::unbox_size_t(x_0);
x_3 = _l_s5_usize_s4_modn(x_2, x_1);
return x_3;
}
}
obj* _init__l_s5_usize_s2_lt_s6___main() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s5_usize_s2_lt() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s5_usize_s2_le_s6___main() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s5_usize_s2_le() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s5_usize_s9_has__zero() {
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_112; obj* x_114; obj* x_115; obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; obj* x_127; obj* x_129; obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_139; obj* x_140; obj* x_142; obj* x_144; obj* x_145; obj* x_147; obj* x_149; obj* x_150; obj* x_152; obj* x_154; obj* x_155; obj* x_157; obj* x_159; obj* x_160; obj* x_162; obj* x_164; obj* x_165; obj* x_167; obj* x_169; obj* x_170; obj* x_172; obj* x_174; obj* x_175; obj* x_177; obj* x_179; obj* x_180; obj* x_182; obj* x_184; obj* x_185; obj* x_187; obj* x_189; obj* x_190; obj* x_192; obj* x_194; obj* x_195; obj* x_197; obj* x_199; obj* x_200; obj* x_202; obj* x_204; obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_215; obj* x_217; obj* x_219; obj* x_220; obj* x_222; obj* x_224; obj* x_225; obj* x_227; obj* x_229; obj* x_230; obj* x_232; obj* x_234; obj* x_235; obj* x_237; obj* x_239; obj* x_240; obj* x_242; obj* x_244; obj* x_245; obj* x_247; obj* x_249; obj* x_250; obj* x_252; obj* x_254; obj* x_255; obj* x_257; obj* x_259; obj* x_260; obj* x_262; obj* x_264; obj* x_265; obj* x_267; obj* x_269; obj* x_270; obj* x_272; obj* x_274; obj* x_275; obj* x_277; obj* x_279; obj* x_280; obj* x_282; obj* x_284; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_292; obj* x_294; obj* x_295; obj* x_297; obj* x_299; obj* x_300; obj* x_302; obj* x_304; obj* x_305; obj* x_309; obj* x_310; obj* x_314; obj* x_315; obj* x_317; obj* x_319; obj* x_320; obj* x_323; obj* x_325; obj* x_328; obj* x_331; obj* x_334; obj* x_337; obj* x_340; obj* x_343; obj* x_346; obj* x_349; obj* x_352; obj* x_355; obj* x_358; obj* x_361; obj* x_364; obj* x_367; obj* x_370; obj* x_373; obj* x_376; obj* x_379; obj* x_382; obj* x_385; obj* x_388; obj* x_391; obj* x_394; obj* x_397; obj* x_400; obj* x_403; obj* x_406; obj* x_409; obj* x_412; obj* x_415; obj* x_418; obj* x_421; obj* x_424; obj* x_427; obj* x_430; obj* x_433; obj* x_436; obj* x_439; obj* x_442; obj* x_445; obj* x_448; obj* x_451; obj* x_454; obj* x_457; obj* x_460; obj* x_463; obj* x_466; obj* x_469; obj* x_472; obj* x_475; obj* x_478; obj* x_481; obj* x_484; obj* x_487; obj* x_490; obj* x_493; obj* x_496; obj* x_499; obj* x_502; obj* x_505; obj* x_508; obj* x_511; obj* x_514; obj* x_515; 
x_0 = lean::mk_nat_obj(2u);
x_1 = lean::mk_nat_obj(63u);
lean::inc(x_0);
x_3 = _l_s3_nat_s3_pow_s6___main(x_0, x_1);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_mul(x_3, x_4);
lean::dec(x_3);
x_7 = lean::mk_nat_obj(62u);
lean::inc(x_0);
x_9 = _l_s3_nat_s3_pow_s6___main(x_0, x_7);
x_10 = lean::nat_mul(x_9, x_4);
lean::dec(x_9);
x_12 = lean::mk_nat_obj(61u);
lean::inc(x_0);
x_14 = _l_s3_nat_s3_pow_s6___main(x_0, x_12);
x_15 = lean::nat_mul(x_14, x_4);
lean::dec(x_14);
x_17 = lean::mk_nat_obj(60u);
lean::inc(x_0);
x_19 = _l_s3_nat_s3_pow_s6___main(x_0, x_17);
x_20 = lean::nat_mul(x_19, x_4);
lean::dec(x_19);
x_22 = lean::mk_nat_obj(59u);
lean::inc(x_0);
x_24 = _l_s3_nat_s3_pow_s6___main(x_0, x_22);
x_25 = lean::nat_mul(x_24, x_4);
lean::dec(x_24);
x_27 = lean::mk_nat_obj(58u);
lean::inc(x_0);
x_29 = _l_s3_nat_s3_pow_s6___main(x_0, x_27);
x_30 = lean::nat_mul(x_29, x_4);
lean::dec(x_29);
x_32 = lean::mk_nat_obj(57u);
lean::inc(x_0);
x_34 = _l_s3_nat_s3_pow_s6___main(x_0, x_32);
x_35 = lean::nat_mul(x_34, x_4);
lean::dec(x_34);
x_37 = lean::mk_nat_obj(56u);
lean::inc(x_0);
x_39 = _l_s3_nat_s3_pow_s6___main(x_0, x_37);
x_40 = lean::nat_mul(x_39, x_4);
lean::dec(x_39);
x_42 = lean::mk_nat_obj(55u);
lean::inc(x_0);
x_44 = _l_s3_nat_s3_pow_s6___main(x_0, x_42);
x_45 = lean::nat_mul(x_44, x_4);
lean::dec(x_44);
x_47 = lean::mk_nat_obj(54u);
lean::inc(x_0);
x_49 = _l_s3_nat_s3_pow_s6___main(x_0, x_47);
x_50 = lean::nat_mul(x_49, x_4);
lean::dec(x_49);
x_52 = lean::mk_nat_obj(53u);
lean::inc(x_0);
x_54 = _l_s3_nat_s3_pow_s6___main(x_0, x_52);
x_55 = lean::nat_mul(x_54, x_4);
lean::dec(x_54);
x_57 = lean::mk_nat_obj(52u);
lean::inc(x_0);
x_59 = _l_s3_nat_s3_pow_s6___main(x_0, x_57);
x_60 = lean::nat_mul(x_59, x_4);
lean::dec(x_59);
x_62 = lean::mk_nat_obj(51u);
lean::inc(x_0);
x_64 = _l_s3_nat_s3_pow_s6___main(x_0, x_62);
x_65 = lean::nat_mul(x_64, x_4);
lean::dec(x_64);
x_67 = lean::mk_nat_obj(50u);
lean::inc(x_0);
x_69 = _l_s3_nat_s3_pow_s6___main(x_0, x_67);
x_70 = lean::nat_mul(x_69, x_4);
lean::dec(x_69);
x_72 = lean::mk_nat_obj(49u);
lean::inc(x_0);
x_74 = _l_s3_nat_s3_pow_s6___main(x_0, x_72);
x_75 = lean::nat_mul(x_74, x_4);
lean::dec(x_74);
x_77 = lean::mk_nat_obj(48u);
lean::inc(x_0);
x_79 = _l_s3_nat_s3_pow_s6___main(x_0, x_77);
x_80 = lean::nat_mul(x_79, x_4);
lean::dec(x_79);
x_82 = lean::mk_nat_obj(47u);
lean::inc(x_0);
x_84 = _l_s3_nat_s3_pow_s6___main(x_0, x_82);
x_85 = lean::nat_mul(x_84, x_4);
lean::dec(x_84);
x_87 = lean::mk_nat_obj(46u);
lean::inc(x_0);
x_89 = _l_s3_nat_s3_pow_s6___main(x_0, x_87);
x_90 = lean::nat_mul(x_89, x_4);
lean::dec(x_89);
x_92 = lean::mk_nat_obj(45u);
lean::inc(x_0);
x_94 = _l_s3_nat_s3_pow_s6___main(x_0, x_92);
x_95 = lean::nat_mul(x_94, x_4);
lean::dec(x_94);
x_97 = lean::mk_nat_obj(44u);
lean::inc(x_0);
x_99 = _l_s3_nat_s3_pow_s6___main(x_0, x_97);
x_100 = lean::nat_mul(x_99, x_4);
lean::dec(x_99);
x_102 = lean::mk_nat_obj(43u);
lean::inc(x_0);
x_104 = _l_s3_nat_s3_pow_s6___main(x_0, x_102);
x_105 = lean::nat_mul(x_104, x_4);
lean::dec(x_104);
x_107 = lean::mk_nat_obj(42u);
lean::inc(x_0);
x_109 = _l_s3_nat_s3_pow_s6___main(x_0, x_107);
x_110 = lean::nat_mul(x_109, x_4);
lean::dec(x_109);
x_112 = lean::mk_nat_obj(41u);
lean::inc(x_0);
x_114 = _l_s3_nat_s3_pow_s6___main(x_0, x_112);
x_115 = lean::nat_mul(x_114, x_4);
lean::dec(x_114);
x_117 = lean::mk_nat_obj(40u);
lean::inc(x_0);
x_119 = _l_s3_nat_s3_pow_s6___main(x_0, x_117);
x_120 = lean::nat_mul(x_119, x_4);
lean::dec(x_119);
x_122 = lean::mk_nat_obj(39u);
lean::inc(x_0);
x_124 = _l_s3_nat_s3_pow_s6___main(x_0, x_122);
x_125 = lean::nat_mul(x_124, x_4);
lean::dec(x_124);
x_127 = lean::mk_nat_obj(38u);
lean::inc(x_0);
x_129 = _l_s3_nat_s3_pow_s6___main(x_0, x_127);
x_130 = lean::nat_mul(x_129, x_4);
lean::dec(x_129);
x_132 = lean::mk_nat_obj(37u);
lean::inc(x_0);
x_134 = _l_s3_nat_s3_pow_s6___main(x_0, x_132);
x_135 = lean::nat_mul(x_134, x_4);
lean::dec(x_134);
x_137 = lean::mk_nat_obj(36u);
lean::inc(x_0);
x_139 = _l_s3_nat_s3_pow_s6___main(x_0, x_137);
x_140 = lean::nat_mul(x_139, x_4);
lean::dec(x_139);
x_142 = lean::mk_nat_obj(35u);
lean::inc(x_0);
x_144 = _l_s3_nat_s3_pow_s6___main(x_0, x_142);
x_145 = lean::nat_mul(x_144, x_4);
lean::dec(x_144);
x_147 = lean::mk_nat_obj(34u);
lean::inc(x_0);
x_149 = _l_s3_nat_s3_pow_s6___main(x_0, x_147);
x_150 = lean::nat_mul(x_149, x_4);
lean::dec(x_149);
x_152 = lean::mk_nat_obj(33u);
lean::inc(x_0);
x_154 = _l_s3_nat_s3_pow_s6___main(x_0, x_152);
x_155 = lean::nat_mul(x_154, x_4);
lean::dec(x_154);
x_157 = lean::mk_nat_obj(32u);
lean::inc(x_0);
x_159 = _l_s3_nat_s3_pow_s6___main(x_0, x_157);
x_160 = lean::nat_mul(x_159, x_4);
lean::dec(x_159);
x_162 = lean::mk_nat_obj(31u);
lean::inc(x_0);
x_164 = _l_s3_nat_s3_pow_s6___main(x_0, x_162);
x_165 = lean::nat_mul(x_164, x_4);
lean::dec(x_164);
x_167 = lean::mk_nat_obj(30u);
lean::inc(x_0);
x_169 = _l_s3_nat_s3_pow_s6___main(x_0, x_167);
x_170 = lean::nat_mul(x_169, x_4);
lean::dec(x_169);
x_172 = lean::mk_nat_obj(29u);
lean::inc(x_0);
x_174 = _l_s3_nat_s3_pow_s6___main(x_0, x_172);
x_175 = lean::nat_mul(x_174, x_4);
lean::dec(x_174);
x_177 = lean::mk_nat_obj(28u);
lean::inc(x_0);
x_179 = _l_s3_nat_s3_pow_s6___main(x_0, x_177);
x_180 = lean::nat_mul(x_179, x_4);
lean::dec(x_179);
x_182 = lean::mk_nat_obj(27u);
lean::inc(x_0);
x_184 = _l_s3_nat_s3_pow_s6___main(x_0, x_182);
x_185 = lean::nat_mul(x_184, x_4);
lean::dec(x_184);
x_187 = lean::mk_nat_obj(26u);
lean::inc(x_0);
x_189 = _l_s3_nat_s3_pow_s6___main(x_0, x_187);
x_190 = lean::nat_mul(x_189, x_4);
lean::dec(x_189);
x_192 = lean::mk_nat_obj(25u);
lean::inc(x_0);
x_194 = _l_s3_nat_s3_pow_s6___main(x_0, x_192);
x_195 = lean::nat_mul(x_194, x_4);
lean::dec(x_194);
x_197 = lean::mk_nat_obj(24u);
lean::inc(x_0);
x_199 = _l_s3_nat_s3_pow_s6___main(x_0, x_197);
x_200 = lean::nat_mul(x_199, x_4);
lean::dec(x_199);
x_202 = lean::mk_nat_obj(23u);
lean::inc(x_0);
x_204 = _l_s3_nat_s3_pow_s6___main(x_0, x_202);
x_205 = lean::nat_mul(x_204, x_4);
lean::dec(x_204);
x_207 = lean::mk_nat_obj(22u);
lean::inc(x_0);
x_209 = _l_s3_nat_s3_pow_s6___main(x_0, x_207);
x_210 = lean::nat_mul(x_209, x_4);
lean::dec(x_209);
x_212 = lean::mk_nat_obj(21u);
lean::inc(x_0);
x_214 = _l_s3_nat_s3_pow_s6___main(x_0, x_212);
x_215 = lean::nat_mul(x_214, x_4);
lean::dec(x_214);
x_217 = lean::mk_nat_obj(20u);
lean::inc(x_0);
x_219 = _l_s3_nat_s3_pow_s6___main(x_0, x_217);
x_220 = lean::nat_mul(x_219, x_4);
lean::dec(x_219);
x_222 = lean::mk_nat_obj(19u);
lean::inc(x_0);
x_224 = _l_s3_nat_s3_pow_s6___main(x_0, x_222);
x_225 = lean::nat_mul(x_224, x_4);
lean::dec(x_224);
x_227 = lean::mk_nat_obj(18u);
lean::inc(x_0);
x_229 = _l_s3_nat_s3_pow_s6___main(x_0, x_227);
x_230 = lean::nat_mul(x_229, x_4);
lean::dec(x_229);
x_232 = lean::mk_nat_obj(17u);
lean::inc(x_0);
x_234 = _l_s3_nat_s3_pow_s6___main(x_0, x_232);
x_235 = lean::nat_mul(x_234, x_4);
lean::dec(x_234);
x_237 = lean::mk_nat_obj(16u);
lean::inc(x_0);
x_239 = _l_s3_nat_s3_pow_s6___main(x_0, x_237);
x_240 = lean::nat_mul(x_239, x_4);
lean::dec(x_239);
x_242 = lean::mk_nat_obj(15u);
lean::inc(x_0);
x_244 = _l_s3_nat_s3_pow_s6___main(x_0, x_242);
x_245 = lean::nat_mul(x_244, x_4);
lean::dec(x_244);
x_247 = lean::mk_nat_obj(14u);
lean::inc(x_0);
x_249 = _l_s3_nat_s3_pow_s6___main(x_0, x_247);
x_250 = lean::nat_mul(x_249, x_4);
lean::dec(x_249);
x_252 = lean::mk_nat_obj(13u);
lean::inc(x_0);
x_254 = _l_s3_nat_s3_pow_s6___main(x_0, x_252);
x_255 = lean::nat_mul(x_254, x_4);
lean::dec(x_254);
x_257 = lean::mk_nat_obj(12u);
lean::inc(x_0);
x_259 = _l_s3_nat_s3_pow_s6___main(x_0, x_257);
x_260 = lean::nat_mul(x_259, x_4);
lean::dec(x_259);
x_262 = lean::mk_nat_obj(11u);
lean::inc(x_0);
x_264 = _l_s3_nat_s3_pow_s6___main(x_0, x_262);
x_265 = lean::nat_mul(x_264, x_4);
lean::dec(x_264);
x_267 = lean::mk_nat_obj(10u);
lean::inc(x_0);
x_269 = _l_s3_nat_s3_pow_s6___main(x_0, x_267);
x_270 = lean::nat_mul(x_269, x_4);
lean::dec(x_269);
x_272 = lean::mk_nat_obj(9u);
lean::inc(x_0);
x_274 = _l_s3_nat_s3_pow_s6___main(x_0, x_272);
x_275 = lean::nat_mul(x_274, x_4);
lean::dec(x_274);
x_277 = lean::mk_nat_obj(8u);
lean::inc(x_0);
x_279 = _l_s3_nat_s3_pow_s6___main(x_0, x_277);
x_280 = lean::nat_mul(x_279, x_4);
lean::dec(x_279);
x_282 = lean::mk_nat_obj(7u);
lean::inc(x_0);
x_284 = _l_s3_nat_s3_pow_s6___main(x_0, x_282);
x_285 = lean::nat_mul(x_284, x_4);
lean::dec(x_284);
x_287 = lean::mk_nat_obj(6u);
lean::inc(x_0);
x_289 = _l_s3_nat_s3_pow_s6___main(x_0, x_287);
x_290 = lean::nat_mul(x_289, x_4);
lean::dec(x_289);
x_292 = lean::mk_nat_obj(5u);
lean::inc(x_0);
x_294 = _l_s3_nat_s3_pow_s6___main(x_0, x_292);
x_295 = lean::nat_mul(x_294, x_4);
lean::dec(x_294);
x_297 = lean::mk_nat_obj(4u);
lean::inc(x_0);
x_299 = _l_s3_nat_s3_pow_s6___main(x_0, x_297);
x_300 = lean::nat_mul(x_299, x_4);
lean::dec(x_299);
x_302 = lean::mk_nat_obj(3u);
lean::inc(x_0);
x_304 = _l_s3_nat_s3_pow_s6___main(x_0, x_302);
x_305 = lean::nat_mul(x_304, x_4);
lean::dec(x_304);
lean::inc(x_0);
lean::inc(x_0);
x_309 = _l_s3_nat_s3_pow_s6___main(x_0, x_0);
x_310 = lean::nat_mul(x_309, x_4);
lean::dec(x_309);
lean::inc(x_4);
lean::inc(x_0);
x_314 = _l_s3_nat_s3_pow_s6___main(x_0, x_4);
x_315 = lean::nat_mul(x_314, x_4);
lean::dec(x_314);
x_317 = lean::mk_nat_obj(0u);
lean::inc(x_317);
x_319 = _l_s3_nat_s3_pow_s6___main(x_0, x_317);
x_320 = lean::nat_mul(x_319, x_4);
lean::dec(x_4);
lean::dec(x_319);
x_323 = lean::nat_add(x_320, x_317);
lean::dec(x_320);
x_325 = lean::nat_add(x_315, x_323);
lean::dec(x_323);
lean::dec(x_315);
x_328 = lean::nat_add(x_310, x_325);
lean::dec(x_325);
lean::dec(x_310);
x_331 = lean::nat_add(x_305, x_328);
lean::dec(x_328);
lean::dec(x_305);
x_334 = lean::nat_add(x_300, x_331);
lean::dec(x_331);
lean::dec(x_300);
x_337 = lean::nat_add(x_295, x_334);
lean::dec(x_334);
lean::dec(x_295);
x_340 = lean::nat_add(x_290, x_337);
lean::dec(x_337);
lean::dec(x_290);
x_343 = lean::nat_add(x_285, x_340);
lean::dec(x_340);
lean::dec(x_285);
x_346 = lean::nat_add(x_280, x_343);
lean::dec(x_343);
lean::dec(x_280);
x_349 = lean::nat_add(x_275, x_346);
lean::dec(x_346);
lean::dec(x_275);
x_352 = lean::nat_add(x_270, x_349);
lean::dec(x_349);
lean::dec(x_270);
x_355 = lean::nat_add(x_265, x_352);
lean::dec(x_352);
lean::dec(x_265);
x_358 = lean::nat_add(x_260, x_355);
lean::dec(x_355);
lean::dec(x_260);
x_361 = lean::nat_add(x_255, x_358);
lean::dec(x_358);
lean::dec(x_255);
x_364 = lean::nat_add(x_250, x_361);
lean::dec(x_361);
lean::dec(x_250);
x_367 = lean::nat_add(x_245, x_364);
lean::dec(x_364);
lean::dec(x_245);
x_370 = lean::nat_add(x_240, x_367);
lean::dec(x_367);
lean::dec(x_240);
x_373 = lean::nat_add(x_235, x_370);
lean::dec(x_370);
lean::dec(x_235);
x_376 = lean::nat_add(x_230, x_373);
lean::dec(x_373);
lean::dec(x_230);
x_379 = lean::nat_add(x_225, x_376);
lean::dec(x_376);
lean::dec(x_225);
x_382 = lean::nat_add(x_220, x_379);
lean::dec(x_379);
lean::dec(x_220);
x_385 = lean::nat_add(x_215, x_382);
lean::dec(x_382);
lean::dec(x_215);
x_388 = lean::nat_add(x_210, x_385);
lean::dec(x_385);
lean::dec(x_210);
x_391 = lean::nat_add(x_205, x_388);
lean::dec(x_388);
lean::dec(x_205);
x_394 = lean::nat_add(x_200, x_391);
lean::dec(x_391);
lean::dec(x_200);
x_397 = lean::nat_add(x_195, x_394);
lean::dec(x_394);
lean::dec(x_195);
x_400 = lean::nat_add(x_190, x_397);
lean::dec(x_397);
lean::dec(x_190);
x_403 = lean::nat_add(x_185, x_400);
lean::dec(x_400);
lean::dec(x_185);
x_406 = lean::nat_add(x_180, x_403);
lean::dec(x_403);
lean::dec(x_180);
x_409 = lean::nat_add(x_175, x_406);
lean::dec(x_406);
lean::dec(x_175);
x_412 = lean::nat_add(x_170, x_409);
lean::dec(x_409);
lean::dec(x_170);
x_415 = lean::nat_add(x_165, x_412);
lean::dec(x_412);
lean::dec(x_165);
x_418 = lean::nat_add(x_160, x_415);
lean::dec(x_415);
lean::dec(x_160);
x_421 = lean::nat_add(x_155, x_418);
lean::dec(x_418);
lean::dec(x_155);
x_424 = lean::nat_add(x_150, x_421);
lean::dec(x_421);
lean::dec(x_150);
x_427 = lean::nat_add(x_145, x_424);
lean::dec(x_424);
lean::dec(x_145);
x_430 = lean::nat_add(x_140, x_427);
lean::dec(x_427);
lean::dec(x_140);
x_433 = lean::nat_add(x_135, x_430);
lean::dec(x_430);
lean::dec(x_135);
x_436 = lean::nat_add(x_130, x_433);
lean::dec(x_433);
lean::dec(x_130);
x_439 = lean::nat_add(x_125, x_436);
lean::dec(x_436);
lean::dec(x_125);
x_442 = lean::nat_add(x_120, x_439);
lean::dec(x_439);
lean::dec(x_120);
x_445 = lean::nat_add(x_115, x_442);
lean::dec(x_442);
lean::dec(x_115);
x_448 = lean::nat_add(x_110, x_445);
lean::dec(x_445);
lean::dec(x_110);
x_451 = lean::nat_add(x_105, x_448);
lean::dec(x_448);
lean::dec(x_105);
x_454 = lean::nat_add(x_100, x_451);
lean::dec(x_451);
lean::dec(x_100);
x_457 = lean::nat_add(x_95, x_454);
lean::dec(x_454);
lean::dec(x_95);
x_460 = lean::nat_add(x_90, x_457);
lean::dec(x_457);
lean::dec(x_90);
x_463 = lean::nat_add(x_85, x_460);
lean::dec(x_460);
lean::dec(x_85);
x_466 = lean::nat_add(x_80, x_463);
lean::dec(x_463);
lean::dec(x_80);
x_469 = lean::nat_add(x_75, x_466);
lean::dec(x_466);
lean::dec(x_75);
x_472 = lean::nat_add(x_70, x_469);
lean::dec(x_469);
lean::dec(x_70);
x_475 = lean::nat_add(x_65, x_472);
lean::dec(x_472);
lean::dec(x_65);
x_478 = lean::nat_add(x_60, x_475);
lean::dec(x_475);
lean::dec(x_60);
x_481 = lean::nat_add(x_55, x_478);
lean::dec(x_478);
lean::dec(x_55);
x_484 = lean::nat_add(x_50, x_481);
lean::dec(x_481);
lean::dec(x_50);
x_487 = lean::nat_add(x_45, x_484);
lean::dec(x_484);
lean::dec(x_45);
x_490 = lean::nat_add(x_40, x_487);
lean::dec(x_487);
lean::dec(x_40);
x_493 = lean::nat_add(x_35, x_490);
lean::dec(x_490);
lean::dec(x_35);
x_496 = lean::nat_add(x_30, x_493);
lean::dec(x_493);
lean::dec(x_30);
x_499 = lean::nat_add(x_25, x_496);
lean::dec(x_496);
lean::dec(x_25);
x_502 = lean::nat_add(x_20, x_499);
lean::dec(x_499);
lean::dec(x_20);
x_505 = lean::nat_add(x_15, x_502);
lean::dec(x_502);
lean::dec(x_15);
x_508 = lean::nat_add(x_10, x_505);
lean::dec(x_505);
lean::dec(x_10);
x_511 = lean::nat_add(x_5, x_508);
lean::dec(x_508);
lean::dec(x_5);
x_514 = _l_s3_fin_s7_of__nat(x_511, x_317);
x_515 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_515, 0, x_514);
return x_515;
}
}
obj* _init__l_s5_usize_s8_has__one() {
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_112; obj* x_114; obj* x_115; obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; obj* x_127; obj* x_129; obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_139; obj* x_140; obj* x_142; obj* x_144; obj* x_145; obj* x_147; obj* x_149; obj* x_150; obj* x_152; obj* x_154; obj* x_155; obj* x_157; obj* x_159; obj* x_160; obj* x_162; obj* x_164; obj* x_165; obj* x_167; obj* x_169; obj* x_170; obj* x_172; obj* x_174; obj* x_175; obj* x_177; obj* x_179; obj* x_180; obj* x_182; obj* x_184; obj* x_185; obj* x_187; obj* x_189; obj* x_190; obj* x_192; obj* x_194; obj* x_195; obj* x_197; obj* x_199; obj* x_200; obj* x_202; obj* x_204; obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_215; obj* x_217; obj* x_219; obj* x_220; obj* x_222; obj* x_224; obj* x_225; obj* x_227; obj* x_229; obj* x_230; obj* x_232; obj* x_234; obj* x_235; obj* x_237; obj* x_239; obj* x_240; obj* x_242; obj* x_244; obj* x_245; obj* x_247; obj* x_249; obj* x_250; obj* x_252; obj* x_254; obj* x_255; obj* x_257; obj* x_259; obj* x_260; obj* x_262; obj* x_264; obj* x_265; obj* x_267; obj* x_269; obj* x_270; obj* x_272; obj* x_274; obj* x_275; obj* x_277; obj* x_279; obj* x_280; obj* x_282; obj* x_284; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_292; obj* x_294; obj* x_295; obj* x_297; obj* x_299; obj* x_300; obj* x_302; obj* x_304; obj* x_305; obj* x_309; obj* x_310; obj* x_314; obj* x_315; obj* x_317; obj* x_319; obj* x_320; obj* x_322; obj* x_325; obj* x_328; obj* x_331; obj* x_334; obj* x_337; obj* x_340; obj* x_343; obj* x_346; obj* x_349; obj* x_352; obj* x_355; obj* x_358; obj* x_361; obj* x_364; obj* x_367; obj* x_370; obj* x_373; obj* x_376; obj* x_379; obj* x_382; obj* x_385; obj* x_388; obj* x_391; obj* x_394; obj* x_397; obj* x_400; obj* x_403; obj* x_406; obj* x_409; obj* x_412; obj* x_415; obj* x_418; obj* x_421; obj* x_424; obj* x_427; obj* x_430; obj* x_433; obj* x_436; obj* x_439; obj* x_442; obj* x_445; obj* x_448; obj* x_451; obj* x_454; obj* x_457; obj* x_460; obj* x_463; obj* x_466; obj* x_469; obj* x_472; obj* x_475; obj* x_478; obj* x_481; obj* x_484; obj* x_487; obj* x_490; obj* x_493; obj* x_496; obj* x_499; obj* x_502; obj* x_505; obj* x_508; obj* x_511; obj* x_514; obj* x_515; 
x_0 = lean::mk_nat_obj(2u);
x_1 = lean::mk_nat_obj(63u);
lean::inc(x_0);
x_3 = _l_s3_nat_s3_pow_s6___main(x_0, x_1);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_mul(x_3, x_4);
lean::dec(x_3);
x_7 = lean::mk_nat_obj(62u);
lean::inc(x_0);
x_9 = _l_s3_nat_s3_pow_s6___main(x_0, x_7);
x_10 = lean::nat_mul(x_9, x_4);
lean::dec(x_9);
x_12 = lean::mk_nat_obj(61u);
lean::inc(x_0);
x_14 = _l_s3_nat_s3_pow_s6___main(x_0, x_12);
x_15 = lean::nat_mul(x_14, x_4);
lean::dec(x_14);
x_17 = lean::mk_nat_obj(60u);
lean::inc(x_0);
x_19 = _l_s3_nat_s3_pow_s6___main(x_0, x_17);
x_20 = lean::nat_mul(x_19, x_4);
lean::dec(x_19);
x_22 = lean::mk_nat_obj(59u);
lean::inc(x_0);
x_24 = _l_s3_nat_s3_pow_s6___main(x_0, x_22);
x_25 = lean::nat_mul(x_24, x_4);
lean::dec(x_24);
x_27 = lean::mk_nat_obj(58u);
lean::inc(x_0);
x_29 = _l_s3_nat_s3_pow_s6___main(x_0, x_27);
x_30 = lean::nat_mul(x_29, x_4);
lean::dec(x_29);
x_32 = lean::mk_nat_obj(57u);
lean::inc(x_0);
x_34 = _l_s3_nat_s3_pow_s6___main(x_0, x_32);
x_35 = lean::nat_mul(x_34, x_4);
lean::dec(x_34);
x_37 = lean::mk_nat_obj(56u);
lean::inc(x_0);
x_39 = _l_s3_nat_s3_pow_s6___main(x_0, x_37);
x_40 = lean::nat_mul(x_39, x_4);
lean::dec(x_39);
x_42 = lean::mk_nat_obj(55u);
lean::inc(x_0);
x_44 = _l_s3_nat_s3_pow_s6___main(x_0, x_42);
x_45 = lean::nat_mul(x_44, x_4);
lean::dec(x_44);
x_47 = lean::mk_nat_obj(54u);
lean::inc(x_0);
x_49 = _l_s3_nat_s3_pow_s6___main(x_0, x_47);
x_50 = lean::nat_mul(x_49, x_4);
lean::dec(x_49);
x_52 = lean::mk_nat_obj(53u);
lean::inc(x_0);
x_54 = _l_s3_nat_s3_pow_s6___main(x_0, x_52);
x_55 = lean::nat_mul(x_54, x_4);
lean::dec(x_54);
x_57 = lean::mk_nat_obj(52u);
lean::inc(x_0);
x_59 = _l_s3_nat_s3_pow_s6___main(x_0, x_57);
x_60 = lean::nat_mul(x_59, x_4);
lean::dec(x_59);
x_62 = lean::mk_nat_obj(51u);
lean::inc(x_0);
x_64 = _l_s3_nat_s3_pow_s6___main(x_0, x_62);
x_65 = lean::nat_mul(x_64, x_4);
lean::dec(x_64);
x_67 = lean::mk_nat_obj(50u);
lean::inc(x_0);
x_69 = _l_s3_nat_s3_pow_s6___main(x_0, x_67);
x_70 = lean::nat_mul(x_69, x_4);
lean::dec(x_69);
x_72 = lean::mk_nat_obj(49u);
lean::inc(x_0);
x_74 = _l_s3_nat_s3_pow_s6___main(x_0, x_72);
x_75 = lean::nat_mul(x_74, x_4);
lean::dec(x_74);
x_77 = lean::mk_nat_obj(48u);
lean::inc(x_0);
x_79 = _l_s3_nat_s3_pow_s6___main(x_0, x_77);
x_80 = lean::nat_mul(x_79, x_4);
lean::dec(x_79);
x_82 = lean::mk_nat_obj(47u);
lean::inc(x_0);
x_84 = _l_s3_nat_s3_pow_s6___main(x_0, x_82);
x_85 = lean::nat_mul(x_84, x_4);
lean::dec(x_84);
x_87 = lean::mk_nat_obj(46u);
lean::inc(x_0);
x_89 = _l_s3_nat_s3_pow_s6___main(x_0, x_87);
x_90 = lean::nat_mul(x_89, x_4);
lean::dec(x_89);
x_92 = lean::mk_nat_obj(45u);
lean::inc(x_0);
x_94 = _l_s3_nat_s3_pow_s6___main(x_0, x_92);
x_95 = lean::nat_mul(x_94, x_4);
lean::dec(x_94);
x_97 = lean::mk_nat_obj(44u);
lean::inc(x_0);
x_99 = _l_s3_nat_s3_pow_s6___main(x_0, x_97);
x_100 = lean::nat_mul(x_99, x_4);
lean::dec(x_99);
x_102 = lean::mk_nat_obj(43u);
lean::inc(x_0);
x_104 = _l_s3_nat_s3_pow_s6___main(x_0, x_102);
x_105 = lean::nat_mul(x_104, x_4);
lean::dec(x_104);
x_107 = lean::mk_nat_obj(42u);
lean::inc(x_0);
x_109 = _l_s3_nat_s3_pow_s6___main(x_0, x_107);
x_110 = lean::nat_mul(x_109, x_4);
lean::dec(x_109);
x_112 = lean::mk_nat_obj(41u);
lean::inc(x_0);
x_114 = _l_s3_nat_s3_pow_s6___main(x_0, x_112);
x_115 = lean::nat_mul(x_114, x_4);
lean::dec(x_114);
x_117 = lean::mk_nat_obj(40u);
lean::inc(x_0);
x_119 = _l_s3_nat_s3_pow_s6___main(x_0, x_117);
x_120 = lean::nat_mul(x_119, x_4);
lean::dec(x_119);
x_122 = lean::mk_nat_obj(39u);
lean::inc(x_0);
x_124 = _l_s3_nat_s3_pow_s6___main(x_0, x_122);
x_125 = lean::nat_mul(x_124, x_4);
lean::dec(x_124);
x_127 = lean::mk_nat_obj(38u);
lean::inc(x_0);
x_129 = _l_s3_nat_s3_pow_s6___main(x_0, x_127);
x_130 = lean::nat_mul(x_129, x_4);
lean::dec(x_129);
x_132 = lean::mk_nat_obj(37u);
lean::inc(x_0);
x_134 = _l_s3_nat_s3_pow_s6___main(x_0, x_132);
x_135 = lean::nat_mul(x_134, x_4);
lean::dec(x_134);
x_137 = lean::mk_nat_obj(36u);
lean::inc(x_0);
x_139 = _l_s3_nat_s3_pow_s6___main(x_0, x_137);
x_140 = lean::nat_mul(x_139, x_4);
lean::dec(x_139);
x_142 = lean::mk_nat_obj(35u);
lean::inc(x_0);
x_144 = _l_s3_nat_s3_pow_s6___main(x_0, x_142);
x_145 = lean::nat_mul(x_144, x_4);
lean::dec(x_144);
x_147 = lean::mk_nat_obj(34u);
lean::inc(x_0);
x_149 = _l_s3_nat_s3_pow_s6___main(x_0, x_147);
x_150 = lean::nat_mul(x_149, x_4);
lean::dec(x_149);
x_152 = lean::mk_nat_obj(33u);
lean::inc(x_0);
x_154 = _l_s3_nat_s3_pow_s6___main(x_0, x_152);
x_155 = lean::nat_mul(x_154, x_4);
lean::dec(x_154);
x_157 = lean::mk_nat_obj(32u);
lean::inc(x_0);
x_159 = _l_s3_nat_s3_pow_s6___main(x_0, x_157);
x_160 = lean::nat_mul(x_159, x_4);
lean::dec(x_159);
x_162 = lean::mk_nat_obj(31u);
lean::inc(x_0);
x_164 = _l_s3_nat_s3_pow_s6___main(x_0, x_162);
x_165 = lean::nat_mul(x_164, x_4);
lean::dec(x_164);
x_167 = lean::mk_nat_obj(30u);
lean::inc(x_0);
x_169 = _l_s3_nat_s3_pow_s6___main(x_0, x_167);
x_170 = lean::nat_mul(x_169, x_4);
lean::dec(x_169);
x_172 = lean::mk_nat_obj(29u);
lean::inc(x_0);
x_174 = _l_s3_nat_s3_pow_s6___main(x_0, x_172);
x_175 = lean::nat_mul(x_174, x_4);
lean::dec(x_174);
x_177 = lean::mk_nat_obj(28u);
lean::inc(x_0);
x_179 = _l_s3_nat_s3_pow_s6___main(x_0, x_177);
x_180 = lean::nat_mul(x_179, x_4);
lean::dec(x_179);
x_182 = lean::mk_nat_obj(27u);
lean::inc(x_0);
x_184 = _l_s3_nat_s3_pow_s6___main(x_0, x_182);
x_185 = lean::nat_mul(x_184, x_4);
lean::dec(x_184);
x_187 = lean::mk_nat_obj(26u);
lean::inc(x_0);
x_189 = _l_s3_nat_s3_pow_s6___main(x_0, x_187);
x_190 = lean::nat_mul(x_189, x_4);
lean::dec(x_189);
x_192 = lean::mk_nat_obj(25u);
lean::inc(x_0);
x_194 = _l_s3_nat_s3_pow_s6___main(x_0, x_192);
x_195 = lean::nat_mul(x_194, x_4);
lean::dec(x_194);
x_197 = lean::mk_nat_obj(24u);
lean::inc(x_0);
x_199 = _l_s3_nat_s3_pow_s6___main(x_0, x_197);
x_200 = lean::nat_mul(x_199, x_4);
lean::dec(x_199);
x_202 = lean::mk_nat_obj(23u);
lean::inc(x_0);
x_204 = _l_s3_nat_s3_pow_s6___main(x_0, x_202);
x_205 = lean::nat_mul(x_204, x_4);
lean::dec(x_204);
x_207 = lean::mk_nat_obj(22u);
lean::inc(x_0);
x_209 = _l_s3_nat_s3_pow_s6___main(x_0, x_207);
x_210 = lean::nat_mul(x_209, x_4);
lean::dec(x_209);
x_212 = lean::mk_nat_obj(21u);
lean::inc(x_0);
x_214 = _l_s3_nat_s3_pow_s6___main(x_0, x_212);
x_215 = lean::nat_mul(x_214, x_4);
lean::dec(x_214);
x_217 = lean::mk_nat_obj(20u);
lean::inc(x_0);
x_219 = _l_s3_nat_s3_pow_s6___main(x_0, x_217);
x_220 = lean::nat_mul(x_219, x_4);
lean::dec(x_219);
x_222 = lean::mk_nat_obj(19u);
lean::inc(x_0);
x_224 = _l_s3_nat_s3_pow_s6___main(x_0, x_222);
x_225 = lean::nat_mul(x_224, x_4);
lean::dec(x_224);
x_227 = lean::mk_nat_obj(18u);
lean::inc(x_0);
x_229 = _l_s3_nat_s3_pow_s6___main(x_0, x_227);
x_230 = lean::nat_mul(x_229, x_4);
lean::dec(x_229);
x_232 = lean::mk_nat_obj(17u);
lean::inc(x_0);
x_234 = _l_s3_nat_s3_pow_s6___main(x_0, x_232);
x_235 = lean::nat_mul(x_234, x_4);
lean::dec(x_234);
x_237 = lean::mk_nat_obj(16u);
lean::inc(x_0);
x_239 = _l_s3_nat_s3_pow_s6___main(x_0, x_237);
x_240 = lean::nat_mul(x_239, x_4);
lean::dec(x_239);
x_242 = lean::mk_nat_obj(15u);
lean::inc(x_0);
x_244 = _l_s3_nat_s3_pow_s6___main(x_0, x_242);
x_245 = lean::nat_mul(x_244, x_4);
lean::dec(x_244);
x_247 = lean::mk_nat_obj(14u);
lean::inc(x_0);
x_249 = _l_s3_nat_s3_pow_s6___main(x_0, x_247);
x_250 = lean::nat_mul(x_249, x_4);
lean::dec(x_249);
x_252 = lean::mk_nat_obj(13u);
lean::inc(x_0);
x_254 = _l_s3_nat_s3_pow_s6___main(x_0, x_252);
x_255 = lean::nat_mul(x_254, x_4);
lean::dec(x_254);
x_257 = lean::mk_nat_obj(12u);
lean::inc(x_0);
x_259 = _l_s3_nat_s3_pow_s6___main(x_0, x_257);
x_260 = lean::nat_mul(x_259, x_4);
lean::dec(x_259);
x_262 = lean::mk_nat_obj(11u);
lean::inc(x_0);
x_264 = _l_s3_nat_s3_pow_s6___main(x_0, x_262);
x_265 = lean::nat_mul(x_264, x_4);
lean::dec(x_264);
x_267 = lean::mk_nat_obj(10u);
lean::inc(x_0);
x_269 = _l_s3_nat_s3_pow_s6___main(x_0, x_267);
x_270 = lean::nat_mul(x_269, x_4);
lean::dec(x_269);
x_272 = lean::mk_nat_obj(9u);
lean::inc(x_0);
x_274 = _l_s3_nat_s3_pow_s6___main(x_0, x_272);
x_275 = lean::nat_mul(x_274, x_4);
lean::dec(x_274);
x_277 = lean::mk_nat_obj(8u);
lean::inc(x_0);
x_279 = _l_s3_nat_s3_pow_s6___main(x_0, x_277);
x_280 = lean::nat_mul(x_279, x_4);
lean::dec(x_279);
x_282 = lean::mk_nat_obj(7u);
lean::inc(x_0);
x_284 = _l_s3_nat_s3_pow_s6___main(x_0, x_282);
x_285 = lean::nat_mul(x_284, x_4);
lean::dec(x_284);
x_287 = lean::mk_nat_obj(6u);
lean::inc(x_0);
x_289 = _l_s3_nat_s3_pow_s6___main(x_0, x_287);
x_290 = lean::nat_mul(x_289, x_4);
lean::dec(x_289);
x_292 = lean::mk_nat_obj(5u);
lean::inc(x_0);
x_294 = _l_s3_nat_s3_pow_s6___main(x_0, x_292);
x_295 = lean::nat_mul(x_294, x_4);
lean::dec(x_294);
x_297 = lean::mk_nat_obj(4u);
lean::inc(x_0);
x_299 = _l_s3_nat_s3_pow_s6___main(x_0, x_297);
x_300 = lean::nat_mul(x_299, x_4);
lean::dec(x_299);
x_302 = lean::mk_nat_obj(3u);
lean::inc(x_0);
x_304 = _l_s3_nat_s3_pow_s6___main(x_0, x_302);
x_305 = lean::nat_mul(x_304, x_4);
lean::dec(x_304);
lean::inc(x_0);
lean::inc(x_0);
x_309 = _l_s3_nat_s3_pow_s6___main(x_0, x_0);
x_310 = lean::nat_mul(x_309, x_4);
lean::dec(x_309);
lean::inc(x_4);
lean::inc(x_0);
x_314 = _l_s3_nat_s3_pow_s6___main(x_0, x_4);
x_315 = lean::nat_mul(x_314, x_4);
lean::dec(x_314);
x_317 = lean::mk_nat_obj(0u);
lean::inc(x_317);
x_319 = _l_s3_nat_s3_pow_s6___main(x_0, x_317);
x_320 = lean::nat_mul(x_319, x_4);
lean::dec(x_319);
x_322 = lean::nat_add(x_320, x_317);
lean::dec(x_317);
lean::dec(x_320);
x_325 = lean::nat_add(x_315, x_322);
lean::dec(x_322);
lean::dec(x_315);
x_328 = lean::nat_add(x_310, x_325);
lean::dec(x_325);
lean::dec(x_310);
x_331 = lean::nat_add(x_305, x_328);
lean::dec(x_328);
lean::dec(x_305);
x_334 = lean::nat_add(x_300, x_331);
lean::dec(x_331);
lean::dec(x_300);
x_337 = lean::nat_add(x_295, x_334);
lean::dec(x_334);
lean::dec(x_295);
x_340 = lean::nat_add(x_290, x_337);
lean::dec(x_337);
lean::dec(x_290);
x_343 = lean::nat_add(x_285, x_340);
lean::dec(x_340);
lean::dec(x_285);
x_346 = lean::nat_add(x_280, x_343);
lean::dec(x_343);
lean::dec(x_280);
x_349 = lean::nat_add(x_275, x_346);
lean::dec(x_346);
lean::dec(x_275);
x_352 = lean::nat_add(x_270, x_349);
lean::dec(x_349);
lean::dec(x_270);
x_355 = lean::nat_add(x_265, x_352);
lean::dec(x_352);
lean::dec(x_265);
x_358 = lean::nat_add(x_260, x_355);
lean::dec(x_355);
lean::dec(x_260);
x_361 = lean::nat_add(x_255, x_358);
lean::dec(x_358);
lean::dec(x_255);
x_364 = lean::nat_add(x_250, x_361);
lean::dec(x_361);
lean::dec(x_250);
x_367 = lean::nat_add(x_245, x_364);
lean::dec(x_364);
lean::dec(x_245);
x_370 = lean::nat_add(x_240, x_367);
lean::dec(x_367);
lean::dec(x_240);
x_373 = lean::nat_add(x_235, x_370);
lean::dec(x_370);
lean::dec(x_235);
x_376 = lean::nat_add(x_230, x_373);
lean::dec(x_373);
lean::dec(x_230);
x_379 = lean::nat_add(x_225, x_376);
lean::dec(x_376);
lean::dec(x_225);
x_382 = lean::nat_add(x_220, x_379);
lean::dec(x_379);
lean::dec(x_220);
x_385 = lean::nat_add(x_215, x_382);
lean::dec(x_382);
lean::dec(x_215);
x_388 = lean::nat_add(x_210, x_385);
lean::dec(x_385);
lean::dec(x_210);
x_391 = lean::nat_add(x_205, x_388);
lean::dec(x_388);
lean::dec(x_205);
x_394 = lean::nat_add(x_200, x_391);
lean::dec(x_391);
lean::dec(x_200);
x_397 = lean::nat_add(x_195, x_394);
lean::dec(x_394);
lean::dec(x_195);
x_400 = lean::nat_add(x_190, x_397);
lean::dec(x_397);
lean::dec(x_190);
x_403 = lean::nat_add(x_185, x_400);
lean::dec(x_400);
lean::dec(x_185);
x_406 = lean::nat_add(x_180, x_403);
lean::dec(x_403);
lean::dec(x_180);
x_409 = lean::nat_add(x_175, x_406);
lean::dec(x_406);
lean::dec(x_175);
x_412 = lean::nat_add(x_170, x_409);
lean::dec(x_409);
lean::dec(x_170);
x_415 = lean::nat_add(x_165, x_412);
lean::dec(x_412);
lean::dec(x_165);
x_418 = lean::nat_add(x_160, x_415);
lean::dec(x_415);
lean::dec(x_160);
x_421 = lean::nat_add(x_155, x_418);
lean::dec(x_418);
lean::dec(x_155);
x_424 = lean::nat_add(x_150, x_421);
lean::dec(x_421);
lean::dec(x_150);
x_427 = lean::nat_add(x_145, x_424);
lean::dec(x_424);
lean::dec(x_145);
x_430 = lean::nat_add(x_140, x_427);
lean::dec(x_427);
lean::dec(x_140);
x_433 = lean::nat_add(x_135, x_430);
lean::dec(x_430);
lean::dec(x_135);
x_436 = lean::nat_add(x_130, x_433);
lean::dec(x_433);
lean::dec(x_130);
x_439 = lean::nat_add(x_125, x_436);
lean::dec(x_436);
lean::dec(x_125);
x_442 = lean::nat_add(x_120, x_439);
lean::dec(x_439);
lean::dec(x_120);
x_445 = lean::nat_add(x_115, x_442);
lean::dec(x_442);
lean::dec(x_115);
x_448 = lean::nat_add(x_110, x_445);
lean::dec(x_445);
lean::dec(x_110);
x_451 = lean::nat_add(x_105, x_448);
lean::dec(x_448);
lean::dec(x_105);
x_454 = lean::nat_add(x_100, x_451);
lean::dec(x_451);
lean::dec(x_100);
x_457 = lean::nat_add(x_95, x_454);
lean::dec(x_454);
lean::dec(x_95);
x_460 = lean::nat_add(x_90, x_457);
lean::dec(x_457);
lean::dec(x_90);
x_463 = lean::nat_add(x_85, x_460);
lean::dec(x_460);
lean::dec(x_85);
x_466 = lean::nat_add(x_80, x_463);
lean::dec(x_463);
lean::dec(x_80);
x_469 = lean::nat_add(x_75, x_466);
lean::dec(x_466);
lean::dec(x_75);
x_472 = lean::nat_add(x_70, x_469);
lean::dec(x_469);
lean::dec(x_70);
x_475 = lean::nat_add(x_65, x_472);
lean::dec(x_472);
lean::dec(x_65);
x_478 = lean::nat_add(x_60, x_475);
lean::dec(x_475);
lean::dec(x_60);
x_481 = lean::nat_add(x_55, x_478);
lean::dec(x_478);
lean::dec(x_55);
x_484 = lean::nat_add(x_50, x_481);
lean::dec(x_481);
lean::dec(x_50);
x_487 = lean::nat_add(x_45, x_484);
lean::dec(x_484);
lean::dec(x_45);
x_490 = lean::nat_add(x_40, x_487);
lean::dec(x_487);
lean::dec(x_40);
x_493 = lean::nat_add(x_35, x_490);
lean::dec(x_490);
lean::dec(x_35);
x_496 = lean::nat_add(x_30, x_493);
lean::dec(x_493);
lean::dec(x_30);
x_499 = lean::nat_add(x_25, x_496);
lean::dec(x_496);
lean::dec(x_25);
x_502 = lean::nat_add(x_20, x_499);
lean::dec(x_499);
lean::dec(x_20);
x_505 = lean::nat_add(x_15, x_502);
lean::dec(x_502);
lean::dec(x_15);
x_508 = lean::nat_add(x_10, x_505);
lean::dec(x_505);
lean::dec(x_10);
x_511 = lean::nat_add(x_5, x_508);
lean::dec(x_508);
lean::dec(x_5);
x_514 = _l_s3_fin_s7_of__nat(x_511, x_4);
x_515 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_515, 0, x_514);
return x_515;
}
}
obj* _init__l_s5_usize_s8_has__add() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s3_add_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s8_has__sub() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s3_sub_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s8_has__mul() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s3_mul_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s8_has__mod() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s3_mod_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s9_has__modn() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s4_modn_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s8_has__div() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s3_div_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s7_has__lt() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s5_usize_s7_has__le() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s5_usize_s9_inhabited() {
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_112; obj* x_114; obj* x_115; obj* x_117; obj* x_119; obj* x_120; obj* x_122; obj* x_124; obj* x_125; obj* x_127; obj* x_129; obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_139; obj* x_140; obj* x_142; obj* x_144; obj* x_145; obj* x_147; obj* x_149; obj* x_150; obj* x_152; obj* x_154; obj* x_155; obj* x_157; obj* x_159; obj* x_160; obj* x_162; obj* x_164; obj* x_165; obj* x_167; obj* x_169; obj* x_170; obj* x_172; obj* x_174; obj* x_175; obj* x_177; obj* x_179; obj* x_180; obj* x_182; obj* x_184; obj* x_185; obj* x_187; obj* x_189; obj* x_190; obj* x_192; obj* x_194; obj* x_195; obj* x_197; obj* x_199; obj* x_200; obj* x_202; obj* x_204; obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_215; obj* x_217; obj* x_219; obj* x_220; obj* x_222; obj* x_224; obj* x_225; obj* x_227; obj* x_229; obj* x_230; obj* x_232; obj* x_234; obj* x_235; obj* x_237; obj* x_239; obj* x_240; obj* x_242; obj* x_244; obj* x_245; obj* x_247; obj* x_249; obj* x_250; obj* x_252; obj* x_254; obj* x_255; obj* x_257; obj* x_259; obj* x_260; obj* x_262; obj* x_264; obj* x_265; obj* x_267; obj* x_269; obj* x_270; obj* x_272; obj* x_274; obj* x_275; obj* x_277; obj* x_279; obj* x_280; obj* x_282; obj* x_284; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_292; obj* x_294; obj* x_295; obj* x_297; obj* x_299; obj* x_300; obj* x_302; obj* x_304; obj* x_305; obj* x_309; obj* x_310; obj* x_314; obj* x_315; obj* x_317; obj* x_319; obj* x_320; obj* x_323; obj* x_325; obj* x_328; obj* x_331; obj* x_334; obj* x_337; obj* x_340; obj* x_343; obj* x_346; obj* x_349; obj* x_352; obj* x_355; obj* x_358; obj* x_361; obj* x_364; obj* x_367; obj* x_370; obj* x_373; obj* x_376; obj* x_379; obj* x_382; obj* x_385; obj* x_388; obj* x_391; obj* x_394; obj* x_397; obj* x_400; obj* x_403; obj* x_406; obj* x_409; obj* x_412; obj* x_415; obj* x_418; obj* x_421; obj* x_424; obj* x_427; obj* x_430; obj* x_433; obj* x_436; obj* x_439; obj* x_442; obj* x_445; obj* x_448; obj* x_451; obj* x_454; obj* x_457; obj* x_460; obj* x_463; obj* x_466; obj* x_469; obj* x_472; obj* x_475; obj* x_478; obj* x_481; obj* x_484; obj* x_487; obj* x_490; obj* x_493; obj* x_496; obj* x_499; obj* x_502; obj* x_505; obj* x_508; obj* x_511; obj* x_514; obj* x_515; 
x_0 = lean::mk_nat_obj(2u);
x_1 = lean::mk_nat_obj(63u);
lean::inc(x_0);
x_3 = _l_s3_nat_s3_pow_s6___main(x_0, x_1);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_mul(x_3, x_4);
lean::dec(x_3);
x_7 = lean::mk_nat_obj(62u);
lean::inc(x_0);
x_9 = _l_s3_nat_s3_pow_s6___main(x_0, x_7);
x_10 = lean::nat_mul(x_9, x_4);
lean::dec(x_9);
x_12 = lean::mk_nat_obj(61u);
lean::inc(x_0);
x_14 = _l_s3_nat_s3_pow_s6___main(x_0, x_12);
x_15 = lean::nat_mul(x_14, x_4);
lean::dec(x_14);
x_17 = lean::mk_nat_obj(60u);
lean::inc(x_0);
x_19 = _l_s3_nat_s3_pow_s6___main(x_0, x_17);
x_20 = lean::nat_mul(x_19, x_4);
lean::dec(x_19);
x_22 = lean::mk_nat_obj(59u);
lean::inc(x_0);
x_24 = _l_s3_nat_s3_pow_s6___main(x_0, x_22);
x_25 = lean::nat_mul(x_24, x_4);
lean::dec(x_24);
x_27 = lean::mk_nat_obj(58u);
lean::inc(x_0);
x_29 = _l_s3_nat_s3_pow_s6___main(x_0, x_27);
x_30 = lean::nat_mul(x_29, x_4);
lean::dec(x_29);
x_32 = lean::mk_nat_obj(57u);
lean::inc(x_0);
x_34 = _l_s3_nat_s3_pow_s6___main(x_0, x_32);
x_35 = lean::nat_mul(x_34, x_4);
lean::dec(x_34);
x_37 = lean::mk_nat_obj(56u);
lean::inc(x_0);
x_39 = _l_s3_nat_s3_pow_s6___main(x_0, x_37);
x_40 = lean::nat_mul(x_39, x_4);
lean::dec(x_39);
x_42 = lean::mk_nat_obj(55u);
lean::inc(x_0);
x_44 = _l_s3_nat_s3_pow_s6___main(x_0, x_42);
x_45 = lean::nat_mul(x_44, x_4);
lean::dec(x_44);
x_47 = lean::mk_nat_obj(54u);
lean::inc(x_0);
x_49 = _l_s3_nat_s3_pow_s6___main(x_0, x_47);
x_50 = lean::nat_mul(x_49, x_4);
lean::dec(x_49);
x_52 = lean::mk_nat_obj(53u);
lean::inc(x_0);
x_54 = _l_s3_nat_s3_pow_s6___main(x_0, x_52);
x_55 = lean::nat_mul(x_54, x_4);
lean::dec(x_54);
x_57 = lean::mk_nat_obj(52u);
lean::inc(x_0);
x_59 = _l_s3_nat_s3_pow_s6___main(x_0, x_57);
x_60 = lean::nat_mul(x_59, x_4);
lean::dec(x_59);
x_62 = lean::mk_nat_obj(51u);
lean::inc(x_0);
x_64 = _l_s3_nat_s3_pow_s6___main(x_0, x_62);
x_65 = lean::nat_mul(x_64, x_4);
lean::dec(x_64);
x_67 = lean::mk_nat_obj(50u);
lean::inc(x_0);
x_69 = _l_s3_nat_s3_pow_s6___main(x_0, x_67);
x_70 = lean::nat_mul(x_69, x_4);
lean::dec(x_69);
x_72 = lean::mk_nat_obj(49u);
lean::inc(x_0);
x_74 = _l_s3_nat_s3_pow_s6___main(x_0, x_72);
x_75 = lean::nat_mul(x_74, x_4);
lean::dec(x_74);
x_77 = lean::mk_nat_obj(48u);
lean::inc(x_0);
x_79 = _l_s3_nat_s3_pow_s6___main(x_0, x_77);
x_80 = lean::nat_mul(x_79, x_4);
lean::dec(x_79);
x_82 = lean::mk_nat_obj(47u);
lean::inc(x_0);
x_84 = _l_s3_nat_s3_pow_s6___main(x_0, x_82);
x_85 = lean::nat_mul(x_84, x_4);
lean::dec(x_84);
x_87 = lean::mk_nat_obj(46u);
lean::inc(x_0);
x_89 = _l_s3_nat_s3_pow_s6___main(x_0, x_87);
x_90 = lean::nat_mul(x_89, x_4);
lean::dec(x_89);
x_92 = lean::mk_nat_obj(45u);
lean::inc(x_0);
x_94 = _l_s3_nat_s3_pow_s6___main(x_0, x_92);
x_95 = lean::nat_mul(x_94, x_4);
lean::dec(x_94);
x_97 = lean::mk_nat_obj(44u);
lean::inc(x_0);
x_99 = _l_s3_nat_s3_pow_s6___main(x_0, x_97);
x_100 = lean::nat_mul(x_99, x_4);
lean::dec(x_99);
x_102 = lean::mk_nat_obj(43u);
lean::inc(x_0);
x_104 = _l_s3_nat_s3_pow_s6___main(x_0, x_102);
x_105 = lean::nat_mul(x_104, x_4);
lean::dec(x_104);
x_107 = lean::mk_nat_obj(42u);
lean::inc(x_0);
x_109 = _l_s3_nat_s3_pow_s6___main(x_0, x_107);
x_110 = lean::nat_mul(x_109, x_4);
lean::dec(x_109);
x_112 = lean::mk_nat_obj(41u);
lean::inc(x_0);
x_114 = _l_s3_nat_s3_pow_s6___main(x_0, x_112);
x_115 = lean::nat_mul(x_114, x_4);
lean::dec(x_114);
x_117 = lean::mk_nat_obj(40u);
lean::inc(x_0);
x_119 = _l_s3_nat_s3_pow_s6___main(x_0, x_117);
x_120 = lean::nat_mul(x_119, x_4);
lean::dec(x_119);
x_122 = lean::mk_nat_obj(39u);
lean::inc(x_0);
x_124 = _l_s3_nat_s3_pow_s6___main(x_0, x_122);
x_125 = lean::nat_mul(x_124, x_4);
lean::dec(x_124);
x_127 = lean::mk_nat_obj(38u);
lean::inc(x_0);
x_129 = _l_s3_nat_s3_pow_s6___main(x_0, x_127);
x_130 = lean::nat_mul(x_129, x_4);
lean::dec(x_129);
x_132 = lean::mk_nat_obj(37u);
lean::inc(x_0);
x_134 = _l_s3_nat_s3_pow_s6___main(x_0, x_132);
x_135 = lean::nat_mul(x_134, x_4);
lean::dec(x_134);
x_137 = lean::mk_nat_obj(36u);
lean::inc(x_0);
x_139 = _l_s3_nat_s3_pow_s6___main(x_0, x_137);
x_140 = lean::nat_mul(x_139, x_4);
lean::dec(x_139);
x_142 = lean::mk_nat_obj(35u);
lean::inc(x_0);
x_144 = _l_s3_nat_s3_pow_s6___main(x_0, x_142);
x_145 = lean::nat_mul(x_144, x_4);
lean::dec(x_144);
x_147 = lean::mk_nat_obj(34u);
lean::inc(x_0);
x_149 = _l_s3_nat_s3_pow_s6___main(x_0, x_147);
x_150 = lean::nat_mul(x_149, x_4);
lean::dec(x_149);
x_152 = lean::mk_nat_obj(33u);
lean::inc(x_0);
x_154 = _l_s3_nat_s3_pow_s6___main(x_0, x_152);
x_155 = lean::nat_mul(x_154, x_4);
lean::dec(x_154);
x_157 = lean::mk_nat_obj(32u);
lean::inc(x_0);
x_159 = _l_s3_nat_s3_pow_s6___main(x_0, x_157);
x_160 = lean::nat_mul(x_159, x_4);
lean::dec(x_159);
x_162 = lean::mk_nat_obj(31u);
lean::inc(x_0);
x_164 = _l_s3_nat_s3_pow_s6___main(x_0, x_162);
x_165 = lean::nat_mul(x_164, x_4);
lean::dec(x_164);
x_167 = lean::mk_nat_obj(30u);
lean::inc(x_0);
x_169 = _l_s3_nat_s3_pow_s6___main(x_0, x_167);
x_170 = lean::nat_mul(x_169, x_4);
lean::dec(x_169);
x_172 = lean::mk_nat_obj(29u);
lean::inc(x_0);
x_174 = _l_s3_nat_s3_pow_s6___main(x_0, x_172);
x_175 = lean::nat_mul(x_174, x_4);
lean::dec(x_174);
x_177 = lean::mk_nat_obj(28u);
lean::inc(x_0);
x_179 = _l_s3_nat_s3_pow_s6___main(x_0, x_177);
x_180 = lean::nat_mul(x_179, x_4);
lean::dec(x_179);
x_182 = lean::mk_nat_obj(27u);
lean::inc(x_0);
x_184 = _l_s3_nat_s3_pow_s6___main(x_0, x_182);
x_185 = lean::nat_mul(x_184, x_4);
lean::dec(x_184);
x_187 = lean::mk_nat_obj(26u);
lean::inc(x_0);
x_189 = _l_s3_nat_s3_pow_s6___main(x_0, x_187);
x_190 = lean::nat_mul(x_189, x_4);
lean::dec(x_189);
x_192 = lean::mk_nat_obj(25u);
lean::inc(x_0);
x_194 = _l_s3_nat_s3_pow_s6___main(x_0, x_192);
x_195 = lean::nat_mul(x_194, x_4);
lean::dec(x_194);
x_197 = lean::mk_nat_obj(24u);
lean::inc(x_0);
x_199 = _l_s3_nat_s3_pow_s6___main(x_0, x_197);
x_200 = lean::nat_mul(x_199, x_4);
lean::dec(x_199);
x_202 = lean::mk_nat_obj(23u);
lean::inc(x_0);
x_204 = _l_s3_nat_s3_pow_s6___main(x_0, x_202);
x_205 = lean::nat_mul(x_204, x_4);
lean::dec(x_204);
x_207 = lean::mk_nat_obj(22u);
lean::inc(x_0);
x_209 = _l_s3_nat_s3_pow_s6___main(x_0, x_207);
x_210 = lean::nat_mul(x_209, x_4);
lean::dec(x_209);
x_212 = lean::mk_nat_obj(21u);
lean::inc(x_0);
x_214 = _l_s3_nat_s3_pow_s6___main(x_0, x_212);
x_215 = lean::nat_mul(x_214, x_4);
lean::dec(x_214);
x_217 = lean::mk_nat_obj(20u);
lean::inc(x_0);
x_219 = _l_s3_nat_s3_pow_s6___main(x_0, x_217);
x_220 = lean::nat_mul(x_219, x_4);
lean::dec(x_219);
x_222 = lean::mk_nat_obj(19u);
lean::inc(x_0);
x_224 = _l_s3_nat_s3_pow_s6___main(x_0, x_222);
x_225 = lean::nat_mul(x_224, x_4);
lean::dec(x_224);
x_227 = lean::mk_nat_obj(18u);
lean::inc(x_0);
x_229 = _l_s3_nat_s3_pow_s6___main(x_0, x_227);
x_230 = lean::nat_mul(x_229, x_4);
lean::dec(x_229);
x_232 = lean::mk_nat_obj(17u);
lean::inc(x_0);
x_234 = _l_s3_nat_s3_pow_s6___main(x_0, x_232);
x_235 = lean::nat_mul(x_234, x_4);
lean::dec(x_234);
x_237 = lean::mk_nat_obj(16u);
lean::inc(x_0);
x_239 = _l_s3_nat_s3_pow_s6___main(x_0, x_237);
x_240 = lean::nat_mul(x_239, x_4);
lean::dec(x_239);
x_242 = lean::mk_nat_obj(15u);
lean::inc(x_0);
x_244 = _l_s3_nat_s3_pow_s6___main(x_0, x_242);
x_245 = lean::nat_mul(x_244, x_4);
lean::dec(x_244);
x_247 = lean::mk_nat_obj(14u);
lean::inc(x_0);
x_249 = _l_s3_nat_s3_pow_s6___main(x_0, x_247);
x_250 = lean::nat_mul(x_249, x_4);
lean::dec(x_249);
x_252 = lean::mk_nat_obj(13u);
lean::inc(x_0);
x_254 = _l_s3_nat_s3_pow_s6___main(x_0, x_252);
x_255 = lean::nat_mul(x_254, x_4);
lean::dec(x_254);
x_257 = lean::mk_nat_obj(12u);
lean::inc(x_0);
x_259 = _l_s3_nat_s3_pow_s6___main(x_0, x_257);
x_260 = lean::nat_mul(x_259, x_4);
lean::dec(x_259);
x_262 = lean::mk_nat_obj(11u);
lean::inc(x_0);
x_264 = _l_s3_nat_s3_pow_s6___main(x_0, x_262);
x_265 = lean::nat_mul(x_264, x_4);
lean::dec(x_264);
x_267 = lean::mk_nat_obj(10u);
lean::inc(x_0);
x_269 = _l_s3_nat_s3_pow_s6___main(x_0, x_267);
x_270 = lean::nat_mul(x_269, x_4);
lean::dec(x_269);
x_272 = lean::mk_nat_obj(9u);
lean::inc(x_0);
x_274 = _l_s3_nat_s3_pow_s6___main(x_0, x_272);
x_275 = lean::nat_mul(x_274, x_4);
lean::dec(x_274);
x_277 = lean::mk_nat_obj(8u);
lean::inc(x_0);
x_279 = _l_s3_nat_s3_pow_s6___main(x_0, x_277);
x_280 = lean::nat_mul(x_279, x_4);
lean::dec(x_279);
x_282 = lean::mk_nat_obj(7u);
lean::inc(x_0);
x_284 = _l_s3_nat_s3_pow_s6___main(x_0, x_282);
x_285 = lean::nat_mul(x_284, x_4);
lean::dec(x_284);
x_287 = lean::mk_nat_obj(6u);
lean::inc(x_0);
x_289 = _l_s3_nat_s3_pow_s6___main(x_0, x_287);
x_290 = lean::nat_mul(x_289, x_4);
lean::dec(x_289);
x_292 = lean::mk_nat_obj(5u);
lean::inc(x_0);
x_294 = _l_s3_nat_s3_pow_s6___main(x_0, x_292);
x_295 = lean::nat_mul(x_294, x_4);
lean::dec(x_294);
x_297 = lean::mk_nat_obj(4u);
lean::inc(x_0);
x_299 = _l_s3_nat_s3_pow_s6___main(x_0, x_297);
x_300 = lean::nat_mul(x_299, x_4);
lean::dec(x_299);
x_302 = lean::mk_nat_obj(3u);
lean::inc(x_0);
x_304 = _l_s3_nat_s3_pow_s6___main(x_0, x_302);
x_305 = lean::nat_mul(x_304, x_4);
lean::dec(x_304);
lean::inc(x_0);
lean::inc(x_0);
x_309 = _l_s3_nat_s3_pow_s6___main(x_0, x_0);
x_310 = lean::nat_mul(x_309, x_4);
lean::dec(x_309);
lean::inc(x_4);
lean::inc(x_0);
x_314 = _l_s3_nat_s3_pow_s6___main(x_0, x_4);
x_315 = lean::nat_mul(x_314, x_4);
lean::dec(x_314);
x_317 = lean::mk_nat_obj(0u);
lean::inc(x_317);
x_319 = _l_s3_nat_s3_pow_s6___main(x_0, x_317);
x_320 = lean::nat_mul(x_319, x_4);
lean::dec(x_4);
lean::dec(x_319);
x_323 = lean::nat_add(x_320, x_317);
lean::dec(x_320);
x_325 = lean::nat_add(x_315, x_323);
lean::dec(x_323);
lean::dec(x_315);
x_328 = lean::nat_add(x_310, x_325);
lean::dec(x_325);
lean::dec(x_310);
x_331 = lean::nat_add(x_305, x_328);
lean::dec(x_328);
lean::dec(x_305);
x_334 = lean::nat_add(x_300, x_331);
lean::dec(x_331);
lean::dec(x_300);
x_337 = lean::nat_add(x_295, x_334);
lean::dec(x_334);
lean::dec(x_295);
x_340 = lean::nat_add(x_290, x_337);
lean::dec(x_337);
lean::dec(x_290);
x_343 = lean::nat_add(x_285, x_340);
lean::dec(x_340);
lean::dec(x_285);
x_346 = lean::nat_add(x_280, x_343);
lean::dec(x_343);
lean::dec(x_280);
x_349 = lean::nat_add(x_275, x_346);
lean::dec(x_346);
lean::dec(x_275);
x_352 = lean::nat_add(x_270, x_349);
lean::dec(x_349);
lean::dec(x_270);
x_355 = lean::nat_add(x_265, x_352);
lean::dec(x_352);
lean::dec(x_265);
x_358 = lean::nat_add(x_260, x_355);
lean::dec(x_355);
lean::dec(x_260);
x_361 = lean::nat_add(x_255, x_358);
lean::dec(x_358);
lean::dec(x_255);
x_364 = lean::nat_add(x_250, x_361);
lean::dec(x_361);
lean::dec(x_250);
x_367 = lean::nat_add(x_245, x_364);
lean::dec(x_364);
lean::dec(x_245);
x_370 = lean::nat_add(x_240, x_367);
lean::dec(x_367);
lean::dec(x_240);
x_373 = lean::nat_add(x_235, x_370);
lean::dec(x_370);
lean::dec(x_235);
x_376 = lean::nat_add(x_230, x_373);
lean::dec(x_373);
lean::dec(x_230);
x_379 = lean::nat_add(x_225, x_376);
lean::dec(x_376);
lean::dec(x_225);
x_382 = lean::nat_add(x_220, x_379);
lean::dec(x_379);
lean::dec(x_220);
x_385 = lean::nat_add(x_215, x_382);
lean::dec(x_382);
lean::dec(x_215);
x_388 = lean::nat_add(x_210, x_385);
lean::dec(x_385);
lean::dec(x_210);
x_391 = lean::nat_add(x_205, x_388);
lean::dec(x_388);
lean::dec(x_205);
x_394 = lean::nat_add(x_200, x_391);
lean::dec(x_391);
lean::dec(x_200);
x_397 = lean::nat_add(x_195, x_394);
lean::dec(x_394);
lean::dec(x_195);
x_400 = lean::nat_add(x_190, x_397);
lean::dec(x_397);
lean::dec(x_190);
x_403 = lean::nat_add(x_185, x_400);
lean::dec(x_400);
lean::dec(x_185);
x_406 = lean::nat_add(x_180, x_403);
lean::dec(x_403);
lean::dec(x_180);
x_409 = lean::nat_add(x_175, x_406);
lean::dec(x_406);
lean::dec(x_175);
x_412 = lean::nat_add(x_170, x_409);
lean::dec(x_409);
lean::dec(x_170);
x_415 = lean::nat_add(x_165, x_412);
lean::dec(x_412);
lean::dec(x_165);
x_418 = lean::nat_add(x_160, x_415);
lean::dec(x_415);
lean::dec(x_160);
x_421 = lean::nat_add(x_155, x_418);
lean::dec(x_418);
lean::dec(x_155);
x_424 = lean::nat_add(x_150, x_421);
lean::dec(x_421);
lean::dec(x_150);
x_427 = lean::nat_add(x_145, x_424);
lean::dec(x_424);
lean::dec(x_145);
x_430 = lean::nat_add(x_140, x_427);
lean::dec(x_427);
lean::dec(x_140);
x_433 = lean::nat_add(x_135, x_430);
lean::dec(x_430);
lean::dec(x_135);
x_436 = lean::nat_add(x_130, x_433);
lean::dec(x_433);
lean::dec(x_130);
x_439 = lean::nat_add(x_125, x_436);
lean::dec(x_436);
lean::dec(x_125);
x_442 = lean::nat_add(x_120, x_439);
lean::dec(x_439);
lean::dec(x_120);
x_445 = lean::nat_add(x_115, x_442);
lean::dec(x_442);
lean::dec(x_115);
x_448 = lean::nat_add(x_110, x_445);
lean::dec(x_445);
lean::dec(x_110);
x_451 = lean::nat_add(x_105, x_448);
lean::dec(x_448);
lean::dec(x_105);
x_454 = lean::nat_add(x_100, x_451);
lean::dec(x_451);
lean::dec(x_100);
x_457 = lean::nat_add(x_95, x_454);
lean::dec(x_454);
lean::dec(x_95);
x_460 = lean::nat_add(x_90, x_457);
lean::dec(x_457);
lean::dec(x_90);
x_463 = lean::nat_add(x_85, x_460);
lean::dec(x_460);
lean::dec(x_85);
x_466 = lean::nat_add(x_80, x_463);
lean::dec(x_463);
lean::dec(x_80);
x_469 = lean::nat_add(x_75, x_466);
lean::dec(x_466);
lean::dec(x_75);
x_472 = lean::nat_add(x_70, x_469);
lean::dec(x_469);
lean::dec(x_70);
x_475 = lean::nat_add(x_65, x_472);
lean::dec(x_472);
lean::dec(x_65);
x_478 = lean::nat_add(x_60, x_475);
lean::dec(x_475);
lean::dec(x_60);
x_481 = lean::nat_add(x_55, x_478);
lean::dec(x_478);
lean::dec(x_55);
x_484 = lean::nat_add(x_50, x_481);
lean::dec(x_481);
lean::dec(x_50);
x_487 = lean::nat_add(x_45, x_484);
lean::dec(x_484);
lean::dec(x_45);
x_490 = lean::nat_add(x_40, x_487);
lean::dec(x_487);
lean::dec(x_40);
x_493 = lean::nat_add(x_35, x_490);
lean::dec(x_490);
lean::dec(x_35);
x_496 = lean::nat_add(x_30, x_493);
lean::dec(x_493);
lean::dec(x_30);
x_499 = lean::nat_add(x_25, x_496);
lean::dec(x_496);
lean::dec(x_25);
x_502 = lean::nat_add(x_20, x_499);
lean::dec(x_499);
lean::dec(x_20);
x_505 = lean::nat_add(x_15, x_502);
lean::dec(x_502);
lean::dec(x_15);
x_508 = lean::nat_add(x_10, x_505);
lean::dec(x_505);
lean::dec(x_10);
x_511 = lean::nat_add(x_5, x_508);
lean::dec(x_508);
lean::dec(x_5);
x_514 = _l_s3_fin_s7_of__nat(x_511, x_317);
x_515 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_515, 0, x_514);
return x_515;
}
}
obj* _l_s5_usize_s7_dec__eq_s6___main(size_t x_0, size_t x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_eq(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s5_usize_s7_dec__eq_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s7_dec__eq_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s7_dec__eq(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = _l_s5_usize_s7_dec__eq_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s7_dec__eq_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s7_dec__eq(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s7_dec__lt_s6___main(size_t x_0, size_t x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s5_usize_s7_dec__lt_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s7_dec__lt_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s7_dec__lt(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = _l_s5_usize_s7_dec__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s7_dec__lt_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s7_dec__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s7_dec__le_s6___main(size_t x_0, size_t x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_le(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s5_usize_s7_dec__le_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s7_dec__le_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s7_dec__le(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = _l_s5_usize_s7_dec__le_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s7_dec__le_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s7_dec__le(x_2, x_3);
return x_4;
}
}
obj* _init__l_s5_usize_s13_decidable__eq() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s7_dec__eq_s7___boxed), 2, 0);
return x_0;
}
}
obj* _l_s5_usize_s18_has__decidable__lt(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = _l_s5_usize_s7_dec__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s18_has__decidable__lt_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s18_has__decidable__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s18_has__decidable__le(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = _l_s5_usize_s7_dec__le_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s18_has__decidable__le_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s18_has__decidable__le(x_2, x_3);
return x_4;
}
}
void _l_initialize__l_s4_init_s4_data_s4_uint();
void _l_initialize__l_s4_init_s8_platform();
void _l_initialize__l_s4_init_s4_data_s3_fin_s7_default();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s5_usize() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s4_uint();
 _l_initialize__l_s4_init_s8_platform();
 _l_initialize__l_s4_init_s4_data_s3_fin_s7_default();
 _l_s9_usize__sz = _init__l_s9_usize__sz();
 _l_s5_usize_s7_of__nat_s11___closed__1 = _init__l_s5_usize_s7_of__nat_s11___closed__1();
 _l_s5_usize_s2_lt_s6___main = _init__l_s5_usize_s2_lt_s6___main();
 _l_s5_usize_s2_lt = _init__l_s5_usize_s2_lt();
 _l_s5_usize_s2_le_s6___main = _init__l_s5_usize_s2_le_s6___main();
 _l_s5_usize_s2_le = _init__l_s5_usize_s2_le();
 _l_s5_usize_s9_has__zero = _init__l_s5_usize_s9_has__zero();
 _l_s5_usize_s8_has__one = _init__l_s5_usize_s8_has__one();
 _l_s5_usize_s8_has__add = _init__l_s5_usize_s8_has__add();
 _l_s5_usize_s8_has__sub = _init__l_s5_usize_s8_has__sub();
 _l_s5_usize_s8_has__mul = _init__l_s5_usize_s8_has__mul();
 _l_s5_usize_s8_has__mod = _init__l_s5_usize_s8_has__mod();
 _l_s5_usize_s9_has__modn = _init__l_s5_usize_s9_has__modn();
 _l_s5_usize_s8_has__div = _init__l_s5_usize_s8_has__div();
 _l_s5_usize_s7_has__lt = _init__l_s5_usize_s7_has__lt();
 _l_s5_usize_s7_has__le = _init__l_s5_usize_s7_has__le();
 _l_s5_usize_s9_inhabited = _init__l_s5_usize_s9_inhabited();
 _l_s5_usize_s13_decidable__eq = _init__l_s5_usize_s13_decidable__eq();
}
