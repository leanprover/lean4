// Lean compiler output
// Module: Lean.ErrorExplanation
// Imports: public import Lean.Message public import Lean.EnvExtension public import Lean.DocString.Links import Init.Data.String.TakeDrop import Init.Data.String.Extra import Init.Data.String.Search
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
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_summaryWithSeverity___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_instToJsonMetadata;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3;
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsSorted___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(lean_object*, lean_object*);
static lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0;
static lean_object* l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0;
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23;
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* l_Lean_ErrorExplanation_summaryWithSeverity___closed__1;
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsRaw(lean_object*);
static lean_object* l_Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getErrorExplanations___redArg___closed__0;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
lean_object* l_Lean_MessageSeverity_toString(uint8_t);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0;
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationRaw_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_instFromJsonMessageSeverity_fromJson(lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2;
LEAN_EXPORT uint8_t l_Lean_getErrorExplanations___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_instToJsonMetadata_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25;
static lean_object* l_Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8;
static lean_object* l_Lean_ErrorExplanation_summaryWithSeverity___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17;
static lean_object* l_Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsSorted(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationRaw_x3f(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0___boxed(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_summaryWithSeverity(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_getErrorExplanations___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_ErrorExplanation_instToJsonMetadata___closed__0;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_instToJsonMessageSeverity_toJson(uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
static lean_object* l_Lean_getErrorExplanations___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27;
LEAN_EXPORT lean_object* l_Lean_errorExplanationExt;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_instFromJsonMessageSeverity_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("summary", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ErrorExplanation", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Metadata", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2;
x_3 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4;
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8;
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sinceVersion", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14;
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("severity", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19;
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("removedVersion", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("removedVersion\?", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25;
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0;
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13;
lean_inc(x_1);
x_17 = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_ctor_set_tag(x_17, 0);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec_ref(x_17);
x_30 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18;
lean_inc(x_1);
x_31 = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(x_1, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_40; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_ctor_set_tag(x_31, 0);
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec_ref(x_31);
x_44 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23;
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
x_51 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28;
x_52 = lean_string_append(x_51, x_50);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
else
{
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_54; 
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_15);
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
lean_ctor_set_tag(x_45, 0);
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_45);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_45, 0);
x_59 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_59, 0, x_15);
lean_ctor_set(x_59, 1, x_29);
lean_ctor_set(x_59, 2, x_58);
x_60 = lean_unbox(x_43);
lean_dec(x_43);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_60);
lean_ctor_set(x_45, 0, x_59);
return x_45;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
lean_dec(x_45);
x_62 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_62, 0, x_15);
lean_ctor_set(x_62, 1, x_29);
lean_ctor_set(x_62, 2, x_61);
x_63 = lean_unbox(x_43);
lean_dec(x_43);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_63);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_ctor_set_tag(x_2, 3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___00Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_instToJsonMetadata_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0;
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13;
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
x_15 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18;
x_16 = l_Lean_instToJsonMessageSeverity_toJson(x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
x_19 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23;
x_20 = l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(x_19, x_5);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0;
x_26 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(x_24, x_25);
x_27 = l_Lean_Json_mkObj(x_26);
return x_27;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instToJsonMetadata___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ErrorExplanation_instToJsonMetadata_toJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instToJsonMetadata() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ErrorExplanation_instToJsonMetadata___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_summaryWithSeverity___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_summaryWithSeverity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(") ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_summaryWithSeverity(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_5 = l_Lean_ErrorExplanation_summaryWithSeverity___closed__0;
x_6 = l_Lean_MessageSeverity_toString(x_4);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
x_8 = l_Lean_ErrorExplanation_summaryWithSeverity___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_summaryWithSeverity___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ErrorExplanation_summaryWithSeverity(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_7, x_8, x_4);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_7, x_8, x_4);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(x_1, x_11, x_3, x_9);
return x_12;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(x_11, x_16, x_17, x_4);
lean_dec(x_11);
x_5 = x_18;
goto block_9;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(x_11, x_19, x_20, x_4);
lean_dec(x_11);
x_5 = x_21;
goto block_9;
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(x_1, x_10, x_11, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn___lam__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("errorExplanationExt", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
x_2 = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(2);
x_2 = lean_box(0);
x_3 = l_Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
x_4 = l_Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
x_5 = l_Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
x_6 = l_Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
x_7 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
lean_ctor_set(x_7, 6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
x_3 = l_Lean_registerSimplePersistentEnvExtension___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_errorExplanationExt;
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_box(0);
x_9 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_1, x_5, x_4, x_7, x_8);
lean_dec(x_7);
x_10 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_9, x_2);
lean_dec(x_9);
x_11 = lean_apply_2(x_3, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getErrorExplanation_x3f___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_box(1);
x_9 = lean_alloc_closure((void*)(l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getErrorExplanation_x3f___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationRaw_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_errorExplanationExt;
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_6, x_3, x_1, x_5, x_7);
lean_dec(x_5);
x_9 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationRaw_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getErrorExplanationRaw_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lean_errorExplanationExt;
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_box(0);
x_9 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_1, x_5, x_4, x_7, x_8);
lean_dec(x_7);
x_10 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(x_2, x_9);
lean_dec(x_9);
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_3, lean_box(0), x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_hasErrorExplanation___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_box(1);
x_9 = lean_alloc_closure((void*)(l_Lean_hasErrorExplanation___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_hasErrorExplanation___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_getErrorExplanations___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = 1;
x_6 = l_Lean_Name_toString(x_3, x_5);
x_7 = l_Lean_Name_toString(x_4, x_5);
x_8 = lean_string_dec_lt(x_6, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_getErrorExplanations___redArg___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_getErrorExplanations___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_20; 
x_6 = l_Lean_errorExplanationExt;
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_box(0);
x_10 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_1, x_6, x_5, x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_getErrorExplanations___redArg___lam__2___closed__0;
x_13 = l_Std_DTreeMap_Internal_Impl_foldl___redArg(x_2, x_12, x_10);
x_14 = lean_array_get_size(x_13);
x_20 = lean_nat_dec_eq(x_14, x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_26; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_14, x_21);
x_26 = lean_nat_dec_le(x_11, x_22);
if (x_26 == 0)
{
lean_inc(x_22);
x_23 = x_22;
goto block_25;
}
else
{
x_23 = x_11;
goto block_25;
}
block_25:
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_23, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_inc(x_23);
x_15 = x_23;
x_16 = x_23;
goto block_19;
}
else
{
x_15 = x_23;
x_16 = x_22;
goto block_19;
}
}
}
else
{
lean_object* x_27; 
lean_dec_ref(x_3);
x_27 = lean_apply_2(x_4, lean_box(0), x_13);
return x_27;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), x_3, x_14, x_13, x_15, x_16, lean_box(0), lean_box(0), lean_box(0));
lean_dec(x_16);
x_18 = lean_apply_2(x_4, lean_box(0), x_17);
return x_18;
}
}
}
static lean_object* _init_l_Lean_getErrorExplanations___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getErrorExplanations___redArg___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_getErrorExplanations___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getErrorExplanations___redArg___lam__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Lean_getErrorExplanations___redArg___closed__0;
x_8 = l_Lean_getErrorExplanations___redArg___closed__1;
x_9 = lean_box(1);
x_10 = lean_alloc_closure((void*)(l_Lean_getErrorExplanations___redArg___lam__2), 5, 4);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_7);
lean_closure_set(x_10, 3, x_6);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getErrorExplanations___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Lean_Name_toString(x_4, x_1);
x_7 = l_Lean_Name_toString(x_5, x_1);
x_8 = lean_string_dec_lt(x_6, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(x_4, x_2, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_box(x_4);
x_6 = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_5);
lean_inc(x_2);
x_7 = l_Array_qpartition___redArg(x_1, x_6, x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_nat_dec_le(x_3, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(x_9, x_2, x_8);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_7 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsRaw(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_2 = l_Lean_errorExplanationExt;
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_box(1);
x_6 = lean_box(0);
x_7 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_5, x_2, x_1, x_4, x_6);
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_getErrorExplanations___redArg___lam__2___closed__0;
x_10 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(x_9, x_7);
lean_dec(x_7);
x_11 = lean_array_get_size(x_10);
x_12 = lean_nat_dec_eq(x_11, x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_20; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
x_20 = lean_nat_dec_le(x_8, x_14);
if (x_20 == 0)
{
lean_inc(x_14);
x_15 = x_14;
goto block_19;
}
else
{
x_15 = x_8;
goto block_19;
}
block_19:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_inc(x_15);
x_17 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(x_10, x_15, x_15);
lean_dec(x_15);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(x_10, x_15, x_14);
lean_dec(x_14);
return x_18;
}
}
}
else
{
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsSorted___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getErrorExplanations___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsSorted(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getErrorExplanations___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Lean_Message(uint8_t builtin);
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* initialize_Lean_DocString_Links(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ErrorExplanation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Links(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0 = _init_l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27);
l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28);
l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0 = _init_l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0);
l_Lean_ErrorExplanation_instFromJsonMetadata = _init_l_Lean_ErrorExplanation_instFromJsonMetadata();
lean_mark_persistent(l_Lean_ErrorExplanation_instFromJsonMetadata);
l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0 = _init_l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0();
lean_mark_persistent(l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0);
l_Lean_ErrorExplanation_instToJsonMetadata___closed__0 = _init_l_Lean_ErrorExplanation_instToJsonMetadata___closed__0();
lean_mark_persistent(l_Lean_ErrorExplanation_instToJsonMetadata___closed__0);
l_Lean_ErrorExplanation_instToJsonMetadata = _init_l_Lean_ErrorExplanation_instToJsonMetadata();
lean_mark_persistent(l_Lean_ErrorExplanation_instToJsonMetadata);
l_Lean_ErrorExplanation_summaryWithSeverity___closed__0 = _init_l_Lean_ErrorExplanation_summaryWithSeverity___closed__0();
lean_mark_persistent(l_Lean_ErrorExplanation_summaryWithSeverity___closed__0);
l_Lean_ErrorExplanation_summaryWithSeverity___closed__1 = _init_l_Lean_ErrorExplanation_summaryWithSeverity___closed__1();
lean_mark_persistent(l_Lean_ErrorExplanation_summaryWithSeverity___closed__1);
l_Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_);
l_Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_);
l_Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_);
l_Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_);
l_Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_);
l_Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_errorExplanationExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_errorExplanationExt);
lean_dec_ref(res);
}l_Lean_getErrorExplanations___redArg___lam__2___closed__0 = _init_l_Lean_getErrorExplanations___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lean_getErrorExplanations___redArg___lam__2___closed__0);
l_Lean_getErrorExplanations___redArg___closed__0 = _init_l_Lean_getErrorExplanations___redArg___closed__0();
lean_mark_persistent(l_Lean_getErrorExplanations___redArg___closed__0);
l_Lean_getErrorExplanations___redArg___closed__1 = _init_l_Lean_getErrorExplanations___redArg___closed__1();
lean_mark_persistent(l_Lean_getErrorExplanations___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
