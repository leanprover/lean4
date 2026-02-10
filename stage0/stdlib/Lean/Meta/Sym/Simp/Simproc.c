// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Simproc
// Imports: public import Lean.Meta.Sym.Simp.Result
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
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc = (const lean_object*)&l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc = (const lean_object*)&l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_14 = lean_apply_11(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_15, 0);
lean_dec_ref(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_14);
x_17 = lean_apply_11(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_17;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
else
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec_ref(x_14);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_20);
x_22 = lean_apply_11(x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
x_25 = lean_ctor_get_uint8(x_24, 0);
lean_dec_ref(x_24);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_25);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
uint8_t x_26; 
lean_free_object(x_22);
lean_free_object(x_15);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_27);
x_29 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_3, x_20, x_21, x_27, x_28, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_24, 1, x_31);
lean_ctor_set(x_29, 0, x_24);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_24, 1, x_32);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_24);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_24);
lean_dec_ref(x_27);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
x_39 = lean_ctor_get_uint8(x_24, sizeof(void*)*2);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
lean_inc_ref(x_37);
x_40 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_3, x_20, x_21, x_37, x_38, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_39);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_37);
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
}
}
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_22, 0);
lean_inc(x_48);
lean_dec(x_22);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; lean_object* x_50; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
x_49 = lean_ctor_get_uint8(x_48, 0);
lean_dec_ref(x_48);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_49);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_15);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_15);
x_51 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc_ref(x_52);
x_53 = lean_ctor_get_uint8(x_48, sizeof(void*)*2);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_54 = x_48;
} else {
 lean_dec_ref(x_48);
 x_54 = lean_box(0);
}
lean_inc_ref(x_51);
x_55 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_3, x_20, x_21, x_51, x_52, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(1, 2, 1);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_53);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 1, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_54);
lean_dec_ref(x_51);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
}
}
}
else
{
lean_free_object(x_15);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
return x_22;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_15, 0);
x_64 = lean_ctor_get(x_15, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_63);
x_65 = lean_apply_11(x_2, x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
x_68 = lean_ctor_get_uint8(x_66, 0);
lean_dec_ref(x_66);
x_69 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_67);
x_71 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_72);
x_73 = lean_ctor_get_uint8(x_66, sizeof(void*)*2);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
 x_74 = lean_box(0);
}
lean_inc_ref(x_71);
x_75 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_3, x_63, x_64, x_71, x_72, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(1, 2, 1);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_73);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
lean_dec_ref(x_71);
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_81 = x_75;
} else {
 lean_dec_ref(x_75);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
}
}
else
{
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
return x_65;
}
}
}
else
{
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_andThen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_Simproc_andThen(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_14 = lean_apply_11(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_box(0);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_15, 0);
lean_dec_ref(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_14);
x_18 = lean_apply_12(x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_18;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
else
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec_ref(x_14);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_21);
x_23 = lean_apply_12(x_2, x_16, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
x_26 = lean_ctor_get_uint8(x_25, 0);
lean_dec_ref(x_25);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_26);
lean_ctor_set(x_23, 0, x_15);
return x_23;
}
else
{
uint8_t x_27; 
lean_free_object(x_23);
lean_free_object(x_15);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_28);
x_30 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_3, x_21, x_22, x_28, x_29, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_25, 1, x_32);
lean_ctor_set(x_30, 0, x_25);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_25, 1, x_33);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_25);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_25);
lean_dec_ref(x_28);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
x_40 = lean_ctor_get_uint8(x_25, sizeof(void*)*2);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
lean_inc_ref(x_38);
x_41 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_3, x_21, x_22, x_38, x_39, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_40);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 1, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_38);
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_47 = x_41;
} else {
 lean_dec_ref(x_41);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
return x_48;
}
}
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_23, 0);
lean_inc(x_49);
lean_dec(x_23);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; lean_object* x_51; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
x_50 = lean_ctor_get_uint8(x_49, 0);
lean_dec_ref(x_49);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_50);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_15);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_15);
x_52 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc_ref(x_53);
x_54 = lean_ctor_get_uint8(x_49, sizeof(void*)*2);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
lean_inc_ref(x_52);
x_56 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_3, x_21, x_22, x_52, x_53, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(1, 2, 1);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_54);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_55);
lean_dec_ref(x_52);
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
return x_63;
}
}
}
}
else
{
lean_free_object(x_15);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
return x_23;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_15, 0);
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_64);
x_66 = lean_apply_12(x_2, x_16, x_64, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
x_69 = lean_ctor_get_uint8(x_67, 0);
lean_dec_ref(x_67);
x_70 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_68);
x_72 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_73);
x_74 = lean_ctor_get_uint8(x_67, sizeof(void*)*2);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_75 = x_67;
} else {
 lean_dec_ref(x_67);
 x_75 = lean_box(0);
}
lean_inc_ref(x_72);
x_76 = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(x_3, x_64, x_65, x_72, x_73, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(1, 2, 1);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_74);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_75);
lean_dec_ref(x_72);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_82 = x_76;
} else {
 lean_dec_ref(x_76);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
}
}
else
{
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
return x_66;
}
}
}
else
{
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_14 = lean_apply_11(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_15, 0);
lean_dec_ref(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_14);
x_17 = lean_apply_11(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_17;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
else
{
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Simproc_orElse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_Simproc_orElse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_14 = lean_apply_11(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_15, 0);
lean_dec_ref(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_14);
x_17 = lean_box(0);
x_18 = lean_apply_12(x_2, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_18;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
else
{
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
