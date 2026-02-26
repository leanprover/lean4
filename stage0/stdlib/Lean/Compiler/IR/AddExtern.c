// Lean compiler output
// Module: Lean.Compiler.IR.AddExtern
// Imports: import Init.While import Lean.Compiler.IR.ToIR import Lean.Compiler.LCNF.ToImpureType import Lean.Compiler.LCNF.ToImpure import Lean.Compiler.LCNF.ExplicitBoxing import Lean.Compiler.LCNF.Internalize public import Lean.Compiler.ExternAttr import Lean.Compiler.LCNF.ExplicitRC
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1;
lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___closed__0;
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_addBoxedVersions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_runExplicitRc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 131, 177, 30, 113, 24, 63, 83)}};
static const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1_value;
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2;
lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_addExtern___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_addExtern___closed__0;
static lean_once_cell_t l_Lean_IR_addExtern___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_addExtern___closed__1;
static lean_once_cell_t l_Lean_IR_addExtern___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_addExtern___closed__2;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_add_extern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addExtern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_st_ref_take(x_1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 2);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Name_num___override(x_6, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_8, 2, x_4);
x_14 = lean_st_ref_set(x_1, x_8);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Name_num___override(x_6, x_7);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_7, x_25);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_26);
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 3, x_18);
lean_ctor_set(x_27, 4, x_19);
lean_ctor_set(x_27, 5, x_20);
lean_ctor_set(x_27, 6, x_21);
lean_ctor_set(x_27, 7, x_22);
lean_ctor_set(x_27, 8, x_23);
x_28 = lean_st_ref_set(x_1, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_24);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = lean_st_ref_take(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 3);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_32, 4);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_32, 5);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_32, 6);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_32, 7);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_32, 8);
lean_inc_ref(x_40);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 lean_ctor_release(x_32, 5);
 lean_ctor_release(x_32, 6);
 lean_ctor_release(x_32, 7);
 lean_ctor_release(x_32, 8);
 x_41 = x_32;
} else {
 lean_dec_ref(x_32);
 x_41 = lean_box(0);
}
lean_inc(x_31);
lean_inc(x_30);
x_42 = l_Lean_Name_num___override(x_30, x_31);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_31, x_43);
lean_dec(x_31);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 9, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_34);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_35);
lean_ctor_set(x_46, 4, x_36);
lean_ctor_set(x_46, 5, x_37);
lean_ctor_set(x_46, 6, x_38);
lean_ctor_set(x_46, 7, x_39);
lean_ctor_set(x_46, 8, x_40);
x_47 = lean_st_ref_set(x_1, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_42);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0___redArg(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 7)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_11);
lean_dec_ref(x_5);
x_12 = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_isMarkedBorrowed(x_10);
x_15 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_14);
x_16 = lean_array_push(x_7, x_15);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_16);
goto _start;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_free_object(x_1);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_24);
lean_dec_ref(x_5);
x_25 = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(x_2, x_3);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_isMarkedBorrowed(x_23);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_27);
x_29 = lean_array_push(x_21, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
x_1 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_33 = x_25;
} else {
 lean_dec_ref(x_25);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_1);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_1, 1);
lean_dec(x_36);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_1);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_5);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_6 = l_Lean_Compiler_LCNF_getOtherDeclMonoType(x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(x_9, x_3, x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = 0;
x_18 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_17);
lean_inc_ref(x_19);
x_20 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_19, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_19);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l_Lean_Compiler_LCNF_Decl_internalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_10);
x_11 = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_11);
x_12 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___closed__0, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___closed__0_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___closed__0);
x_13 = lean_array_push(x_12, x_10);
x_14 = l_Lean_Compiler_LCNF_addBoxedVersions(x_13, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Compiler_LCNF_runExplicitRc(x_15, x_4, x_5, x_6, x_7);
return x_16;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_14;
}
}
else
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec_ref(x_4);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_5);
lean_inc_ref(x_4);
x_14 = l_Lean_Compiler_LCNF_toImpureType(x_13, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
lean_ctor_set(x_9, 2, x_15);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_17, x_2, x_9);
x_2 = x_19;
x_3 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_free_object(x_9);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
x_27 = lean_ctor_get(x_9, 2);
x_28 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
lean_inc(x_5);
lean_inc_ref(x_4);
x_29 = l_Lean_Compiler_LCNF_toImpureType(x_27, x_4, x_5);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_uset(x_3, x_2, x_31);
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_28);
x_34 = 1;
x_35 = lean_usize_add(x_2, x_34);
x_36 = lean_array_uset(x_32, x_2, x_33);
x_2 = x_35;
x_3 = x_36;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_39 = x_29;
} else {
 lean_dec_ref(x_29);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(x_7, x_8, x_3, x_4, x_5);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 2);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 2);
x_14 = lean_ctor_get(x_7, 3);
x_15 = lean_array_get_size(x_14);
lean_inc(x_4);
lean_inc_ref(x_3);
x_16 = l_Lean_Compiler_LCNF_lowerResultType(x_13, x_15, x_3, x_4);
lean_dec_ref(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_array_size(x_14);
x_19 = 0;
lean_inc(x_4);
lean_inc_ref(x_3);
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(x_18, x_19, x_14, x_3, x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = 1;
x_23 = 1;
lean_ctor_set(x_7, 3, x_21);
lean_ctor_set(x_7, 2, x_17);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = 0;
x_26 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1);
lean_ctor_set(x_2, 2, x_26);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set_uint8(x_2, sizeof(void*)*3, x_25);
x_27 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1);
x_28 = lean_box(x_22);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___boxed), 8, 3);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_27);
x_30 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3);
x_31 = 2;
x_32 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_29, x_30, x_31, x_3, x_4);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_11);
lean_free_object(x_2);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_free_object(x_7);
lean_dec_ref(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_free_object(x_2);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_16, 0);
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get(x_7, 1);
x_41 = lean_ctor_get(x_7, 2);
x_42 = lean_ctor_get(x_7, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_7);
x_43 = lean_array_get_size(x_42);
lean_inc(x_4);
lean_inc_ref(x_3);
x_44 = l_Lean_Compiler_LCNF_lowerResultType(x_41, x_43, x_3, x_4);
lean_dec_ref(x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_array_size(x_42);
x_47 = 0;
lean_inc(x_4);
lean_inc_ref(x_3);
x_48 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(x_46, x_47, x_42, x_3, x_4);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = 1;
x_51 = 1;
x_52 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_52, 0, x_39);
lean_ctor_set(x_52, 1, x_40);
lean_ctor_set(x_52, 2, x_45);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_1);
x_54 = 0;
x_55 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1);
lean_ctor_set(x_2, 2, x_55);
lean_ctor_set(x_2, 1, x_53);
lean_ctor_set(x_2, 0, x_52);
lean_ctor_set_uint8(x_2, sizeof(void*)*3, x_54);
x_56 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1);
x_57 = lean_box(x_50);
x_58 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___boxed), 8, 3);
lean_closure_set(x_58, 0, x_57);
lean_closure_set(x_58, 1, x_2);
lean_closure_set(x_58, 2, x_56);
x_59 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3);
x_60 = 2;
x_61 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_58, x_59, x_60, x_3, x_4);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_2);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_62 = lean_ctor_get(x_48, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_63 = x_48;
} else {
 lean_dec_ref(x_48);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_2);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_66 = x_44;
} else {
 lean_dec_ref(x_44);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
lean_dec(x_2);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 2);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_68, 3);
lean_inc_ref(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
x_74 = lean_array_get_size(x_72);
lean_inc(x_4);
lean_inc_ref(x_3);
x_75 = l_Lean_Compiler_LCNF_lowerResultType(x_71, x_74, x_3, x_4);
lean_dec_ref(x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_array_size(x_72);
x_78 = 0;
lean_inc(x_4);
lean_inc_ref(x_3);
x_79 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(x_77, x_78, x_72, x_3, x_4);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = 1;
x_82 = 1;
if (lean_is_scalar(x_73)) {
 x_83 = lean_alloc_ctor(0, 4, 1);
} else {
 x_83 = x_73;
}
lean_ctor_set(x_83, 0, x_69);
lean_ctor_set(x_83, 1, x_70);
lean_ctor_set(x_83, 2, x_76);
lean_ctor_set(x_83, 3, x_80);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_1);
x_85 = 0;
x_86 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1);
x_87 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_84);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_85);
x_88 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1);
x_89 = lean_box(x_81);
x_90 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___boxed), 8, 3);
lean_closure_set(x_90, 0, x_89);
lean_closure_set(x_90, 1, x_87);
lean_closure_set(x_90, 2, x_88);
x_91 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3);
x_92 = 2;
x_93 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_90, x_91, x_92, x_3, x_4);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_94 = lean_ctor_get(x_79, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_95 = x_79;
} else {
 lean_dec_ref(x_79);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_97 = lean_ctor_get(x_75, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_98 = x_75;
} else {
 lean_dec_ref(x_75);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1));
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_5 = l_Lean_IR_toIR(x_1, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1));
x_8 = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2);
lean_inc(x_6);
x_9 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_8, x_7, x_6, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_9);
x_10 = l_Lean_IR_addDecls(x_6, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_6);
return x_10;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_IR_addExtern___closed__0, &l_Lean_IR_addExtern___closed__0_once, _init_l_Lean_IR_addExtern___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_addExtern___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_IR_addExtern___closed__1, &l_Lean_IR_addExtern___closed__1_once, _init_l_Lean_IR_addExtern___closed__1);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_add_extern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_21; 
x_21 = l_Lean_isPrivateName(x_1);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_st_ref_take(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 5);
lean_dec(x_25);
lean_inc(x_1);
x_26 = l_Lean_Compiler_LCNF_setDeclPublic(x_24, x_1);
x_27 = lean_obj_once(&l_Lean_IR_addExtern___closed__2, &l_Lean_IR_addExtern___closed__2_once, _init_l_Lean_IR_addExtern___closed__2);
lean_ctor_set(x_22, 5, x_27);
lean_ctor_set(x_22, 0, x_26);
x_28 = lean_st_ref_set(x_4, x_22);
x_6 = x_3;
x_7 = x_4;
x_8 = lean_box(0);
goto block_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
x_31 = lean_ctor_get(x_22, 2);
x_32 = lean_ctor_get(x_22, 3);
x_33 = lean_ctor_get(x_22, 4);
x_34 = lean_ctor_get(x_22, 6);
x_35 = lean_ctor_get(x_22, 7);
x_36 = lean_ctor_get(x_22, 8);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
lean_inc(x_1);
x_37 = l_Lean_Compiler_LCNF_setDeclPublic(x_29, x_1);
x_38 = lean_obj_once(&l_Lean_IR_addExtern___closed__2, &l_Lean_IR_addExtern___closed__2_once, _init_l_Lean_IR_addExtern___closed__2);
x_39 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_39, 2, x_31);
lean_ctor_set(x_39, 3, x_32);
lean_ctor_set(x_39, 4, x_33);
lean_ctor_set(x_39, 5, x_38);
lean_ctor_set(x_39, 6, x_34);
lean_ctor_set(x_39, 7, x_35);
lean_ctor_set(x_39, 8, x_36);
x_40 = lean_st_ref_set(x_4, x_39);
x_6 = x_3;
x_7 = x_4;
x_8 = lean_box(0);
goto block_20;
}
}
else
{
x_6 = x_3;
x_7 = x_4;
x_8 = lean_box(0);
goto block_20;
}
block_20:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_2);
x_9 = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(x_2, x_1, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
x_11 = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(x_2, x_10, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(x_12, x_6, x_7);
lean_dec(x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec_ref(x_6);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addExtern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_add_extern(x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ExplicitBoxing(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
