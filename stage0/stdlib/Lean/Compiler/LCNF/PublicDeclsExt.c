// Lean compiler output
// Module: Lean.Compiler.LCNF.PublicDeclsExt
// Imports: public import Lean.Environment
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
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__0___boxed(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0___closed__0;
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_mkDeclSetExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclSetExt___closed__0_value;
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___closed__1;
static lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___closed__2;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclSetExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclSetExt___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclSetExt___closed__3_value;
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_430278831____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_430278831____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
static const lean_ctor_object l_Lean_Compiler_LCNF_isDeclPublic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_isDeclPublic___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_isDeclPublic___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_isDeclPublic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l_Lean_Compiler_LCNF_isDeclPublic___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_isDeclPublic___closed__1_value;
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isDeclPublic___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_name_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_List_elem___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__0(x_5, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_inc(x_8);
lean_inc(x_7);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_ctor_set(x_3, 1, x_7);
x_14 = l_Lean_NameSet_contains(x_13, x_5);
if (x_14 == 0)
{
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_3);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_NameSet_insert(x_8, x_5);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_3);
x_3 = x_6;
goto _start;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_ctor_set(x_3, 1, x_7);
x_19 = l_Lean_NameSet_contains(x_18, x_5);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_8);
x_2 = x_20;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_NameSet_insert(x_8, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_22);
x_2 = x_23;
x_3 = x_6;
goto _start;
}
}
}
else
{
lean_free_object(x_3);
lean_dec(x_5);
x_3 = x_6;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = l_List_elem___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__0(x_26, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_inc(x_29);
lean_inc(x_28);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_31 = x_2;
} else {
 lean_dec_ref(x_2);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_28);
x_34 = l_Lean_NameSet_contains(x_32, x_26);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_26);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_29);
x_2 = x_35;
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_NameSet_insert(x_29, x_26);
if (lean_is_scalar(x_31)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_31;
}
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_2 = x_38;
x_3 = x_27;
goto _start;
}
}
else
{
lean_dec(x_26);
x_3 = x_27;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_List_lengthTR___redArg(x_5);
x_8 = l_List_lengthTR___redArg(x_6);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0___closed__0;
lean_inc(x_5);
x_11 = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), x_5, x_5, x_9, x_10);
x_12 = l_List_foldl___at___00Lean_Compiler_LCNF_mkDeclSetExt_spec__1(x_2, x_4, x_11);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_mkDeclSetExt___lam__1(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclSetExt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclSetExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_mkDeclSetExt___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclSetExt___lam__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_mkDeclSetExt___closed__2;
x_3 = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclSetExt___closed__3));
x_4 = lean_box(0);
x_5 = l_Lean_registerEnvExtension___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclSetExt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_mkDeclSetExt();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_430278831____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_mkDeclSetExt();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_430278831____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_430278831____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Environment_header(x_1);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 4);
lean_dec_ref(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclPublic___closed__0));
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclPublic___closed__1));
x_18 = lean_string_dec_eq(x_16, x_17);
if (x_18 == 0)
{
x_7 = x_2;
goto block_14;
}
else
{
x_7 = x_15;
goto block_14;
}
}
else
{
x_7 = x_2;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_6, x_8, x_1, x_9, x_10);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_NameSet_contains(x_12, x_7);
lean_dec(x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isDeclPublic___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_isDeclPublic(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lean_NameSet_insert(x_5, x_1);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_NameSet_insert(x_9, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc_ref(x_1);
x_3 = l_Lean_Compiler_LCNF_isDeclPublic(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_setDeclPublic___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_box(0);
x_8 = l_Lean_EnvExtension_modifyState___redArg(x_4, x_1, x_6, x_5, x_7);
lean_dec(x_5);
return x_8;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkDeclSetExt___lam__0___closed__0);
l_Lean_Compiler_LCNF_mkDeclSetExt___closed__1 = _init_l_Lean_Compiler_LCNF_mkDeclSetExt___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkDeclSetExt___closed__1);
l_Lean_Compiler_LCNF_mkDeclSetExt___closed__2 = _init_l_Lean_Compiler_LCNF_mkDeclSetExt___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkDeclSetExt___closed__2);
if (builtin) {res = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_430278831____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
