// Lean compiler output
// Module: Lean.LibrarySuggestions.SymbolFrequency
// Imports: public import Lean.Meta.Basic import Lean.LibrarySuggestions.Basic
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LibrarySuggestions_isDeniedPremise(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_set_heartbeats(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_1332954629____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_1332954629____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "library suggestion initialization"};
static const lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__0_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__1;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__2;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__3;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__1_value;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__2;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__3;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__5;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__7;
static const lean_array_object l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__8 = (const lean_object*)&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__8_value;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__9;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__10;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__11;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__12;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__13;
static lean_once_cell_t l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__14;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_1332954629____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = lean_box(0);
v___x_3_ = lean_st_mk_ref(v___x_2_);
v___x_4_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_1332954629____hygCtx___hyg_2____boxed(lean_object* v_a_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_1332954629____hygCtx___hyg_2_();
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___lam__0(lean_object* v_val_7_, lean_object* v_a_x3f_8_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_io_set_heartbeats(v_val_7_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___lam__0___boxed(lean_object* v_val_12_, lean_object* v_a_x3f_13_, lean_object* v___y_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___lam__0(v_val_12_, v_a_x3f_13_);
lean_dec(v_a_x3f_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg(lean_object* v_x_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___closed__0));
v___x_22_ = l_Lean_Core_checkSystem(v___x_21_, v_a_18_, v_a_19_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v___x_23_; lean_object* v_toCold_24_; lean_object* v_currRecDepth_25_; lean_object* v_ref_26_; uint8_t v_diag_27_; uint8_t v_suppressElabErrors_28_; lean_object* v_fileName_29_; lean_object* v_fileMap_30_; lean_object* v_options_31_; lean_object* v_maxRecDepth_32_; lean_object* v_currNamespace_33_; lean_object* v_openDecls_34_; lean_object* v_initHeartbeats_35_; lean_object* v_quotContext_36_; lean_object* v_currMacroScope_37_; lean_object* v_cancelTk_x3f_38_; lean_object* v_inheritedTraceOptions_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
lean_dec_ref_known(v___x_22_, 1);
v___x_23_ = lean_io_get_num_heartbeats();
v_toCold_24_ = lean_ctor_get(v_a_18_, 0);
v_currRecDepth_25_ = lean_ctor_get(v_a_18_, 1);
v_ref_26_ = lean_ctor_get(v_a_18_, 2);
v_diag_27_ = lean_ctor_get_uint8(v_a_18_, sizeof(void*)*3);
v_suppressElabErrors_28_ = lean_ctor_get_uint8(v_a_18_, sizeof(void*)*3 + 1);
v_fileName_29_ = lean_ctor_get(v_toCold_24_, 0);
v_fileMap_30_ = lean_ctor_get(v_toCold_24_, 1);
v_options_31_ = lean_ctor_get(v_toCold_24_, 2);
v_maxRecDepth_32_ = lean_ctor_get(v_toCold_24_, 3);
v_currNamespace_33_ = lean_ctor_get(v_toCold_24_, 4);
v_openDecls_34_ = lean_ctor_get(v_toCold_24_, 5);
v_initHeartbeats_35_ = lean_ctor_get(v_toCold_24_, 6);
v_quotContext_36_ = lean_ctor_get(v_toCold_24_, 8);
v_currMacroScope_37_ = lean_ctor_get(v_toCold_24_, 9);
v_cancelTk_x3f_38_ = lean_ctor_get(v_toCold_24_, 10);
v_inheritedTraceOptions_39_ = lean_ctor_get(v_toCold_24_, 11);
v___x_40_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inheritedTraceOptions_39_);
lean_inc(v_cancelTk_x3f_38_);
lean_inc(v_currMacroScope_37_);
lean_inc(v_quotContext_36_);
lean_inc(v_initHeartbeats_35_);
lean_inc(v_openDecls_34_);
lean_inc(v_currNamespace_33_);
lean_inc(v_maxRecDepth_32_);
lean_inc_ref(v_options_31_);
lean_inc_ref(v_fileMap_30_);
lean_inc_ref(v_fileName_29_);
v___x_41_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_41_, 0, v_fileName_29_);
lean_ctor_set(v___x_41_, 1, v_fileMap_30_);
lean_ctor_set(v___x_41_, 2, v_options_31_);
lean_ctor_set(v___x_41_, 3, v_maxRecDepth_32_);
lean_ctor_set(v___x_41_, 4, v_currNamespace_33_);
lean_ctor_set(v___x_41_, 5, v_openDecls_34_);
lean_ctor_set(v___x_41_, 6, v_initHeartbeats_35_);
lean_ctor_set(v___x_41_, 7, v___x_40_);
lean_ctor_set(v___x_41_, 8, v_quotContext_36_);
lean_ctor_set(v___x_41_, 9, v_currMacroScope_37_);
lean_ctor_set(v___x_41_, 10, v_cancelTk_x3f_38_);
lean_ctor_set(v___x_41_, 11, v_inheritedTraceOptions_39_);
lean_inc(v_ref_26_);
lean_inc(v_currRecDepth_25_);
v___x_42_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v_currRecDepth_25_);
lean_ctor_set(v___x_42_, 2, v_ref_26_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3, v_diag_27_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 1, v_suppressElabErrors_28_);
lean_inc(v_a_19_);
v___x_43_ = lean_apply_3(v_x_17_, v___x_42_, v_a_19_, lean_box(0));
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_60_; 
v_a_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_60_ == 0)
{
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_60_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_60_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_49_; 
lean_inc(v_a_44_);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 1);
v___x_49_ = v___x_46_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_44_);
v___x_49_ = v_reuseFailAlloc_59_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_object* v___x_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_57_; 
v___x_50_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___lam__0(v___x_23_, v___x_49_);
lean_dec_ref(v___x_49_);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_57_ == 0)
{
lean_object* v_unused_58_; 
v_unused_58_ = lean_ctor_get(v___x_50_, 0);
lean_dec(v_unused_58_);
v___x_52_ = v___x_50_;
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
else
{
lean_dec(v___x_50_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 0, v_a_44_);
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_44_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
}
else
{
lean_object* v_a_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
v_a_61_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___x_43_, 1);
v___x_62_ = lean_box(0);
v___x_63_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___lam__0(v___x_23_, v___x_62_);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_70_ == 0)
{
lean_object* v_unused_71_; 
v_unused_71_ = lean_ctor_get(v___x_63_, 0);
lean_dec(v_unused_71_);
v___x_65_ = v___x_63_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_dec(v___x_63_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 1);
lean_ctor_set(v___x_65_, 0, v_a_61_);
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_61_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
else
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
lean_dec_ref(v_x_17_);
v_a_72_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v___x_22_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_22_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___boxed(lean_object* v_x_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg(v_x_80_, v_a_81_, v_a_82_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats(lean_object* v_00_u03b1_85_, lean_object* v_x_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg(v_x_86_, v_a_87_, v_a_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___boxed(lean_object* v_00_u03b1_91_, lean_object* v_x_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats(v_00_u03b1_91_, v_x_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0(lean_object* v_count_97_){
_start:
{
lean_object* v___y_99_; 
if (lean_obj_tag(v_count_97_) == 0)
{
lean_object* v___x_103_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___y_99_ = v___x_103_;
goto v___jp_98_;
}
else
{
lean_object* v_val_104_; 
v_val_104_ = lean_ctor_get(v_count_97_, 0);
v___y_99_ = v_val_104_;
goto v___jp_98_;
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_add(v___y_99_, v___x_100_);
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0___boxed(lean_object* v_count_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0(v_count_105_);
lean_dec(v_count_105_);
return v_res_106_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_box(0);
v___x_108_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg(lean_object* v_k_109_, lean_object* v_t_110_){
_start:
{
if (lean_obj_tag(v_t_110_) == 0)
{
lean_object* v_size_111_; lean_object* v_k_112_; lean_object* v_v_113_; lean_object* v_l_114_; lean_object* v_r_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_130_; 
v_size_111_ = lean_ctor_get(v_t_110_, 0);
v_k_112_ = lean_ctor_get(v_t_110_, 1);
v_v_113_ = lean_ctor_get(v_t_110_, 2);
v_l_114_ = lean_ctor_get(v_t_110_, 3);
v_r_115_ = lean_ctor_get(v_t_110_, 4);
v_isSharedCheck_130_ = !lean_is_exclusive(v_t_110_);
if (v_isSharedCheck_130_ == 0)
{
v___x_117_ = v_t_110_;
v_isShared_118_ = v_isSharedCheck_130_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_r_115_);
lean_inc(v_l_114_);
lean_inc(v_v_113_);
lean_inc(v_k_112_);
lean_inc(v_size_111_);
lean_dec(v_t_110_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_130_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
uint8_t v___x_119_; 
v___x_119_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_109_, v_k_112_);
switch(v___x_119_)
{
case 0:
{
lean_object* v_impl_120_; lean_object* v___x_121_; 
lean_del_object(v___x_117_);
lean_dec(v_size_111_);
v_impl_120_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg(v_k_109_, v_l_114_);
v___x_121_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_112_, v_v_113_, v_impl_120_, v_r_115_);
return v___x_121_;
}
case 1:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_val_124_; lean_object* v___x_126_; 
lean_dec(v_k_112_);
v___x_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_122_, 0, v_v_113_);
v___x_123_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0(v___x_122_);
lean_dec_ref_known(v___x_122_, 1);
v_val_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_val_124_);
lean_dec(v___x_123_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 2, v_val_124_);
lean_ctor_set(v___x_117_, 1, v_k_109_);
v___x_126_ = v___x_117_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_size_111_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_k_109_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_val_124_);
lean_ctor_set(v_reuseFailAlloc_127_, 3, v_l_114_);
lean_ctor_set(v_reuseFailAlloc_127_, 4, v_r_115_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
default: 
{
lean_object* v_impl_128_; lean_object* v___x_129_; 
lean_del_object(v___x_117_);
lean_dec(v_size_111_);
v_impl_128_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg(v_k_109_, v_r_115_);
v___x_129_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_112_, v_v_113_, v_l_114_, v_impl_128_);
return v___x_129_;
}
}
}
}
else
{
lean_object* v___x_131_; lean_object* v_val_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_131_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___closed__0);
v_val_132_ = lean_ctor_get(v___x_131_, 0);
v___x_133_ = lean_unsigned_to_nat(1u);
lean_inc(v_val_132_);
v___x_134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v_k_109_);
lean_ctor_set(v___x_134_, 2, v_val_132_);
lean_ctor_set(v___x_134_, 3, v_t_110_);
lean_ctor_set(v___x_134_, 4, v_t_110_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___lam__0(lean_object* v_n_135_, lean_object* v_acc_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg(v_n_135_, v_acc_136_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___lam__0___boxed(lean_object* v_n_144_, lean_object* v_acc_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___lam__0(v_n_144_, v_acc_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_151_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__1(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(64u);
v___x_154_ = l_Lean_mkPtrSet___redArg(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__2(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_box(0);
v___x_156_ = lean_unsigned_to_nat(16u);
v___x_157_ = lean_mk_array(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__3(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__2, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__2_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__2);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__4(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__3, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__3);
v___x_162_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__1, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__1_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__1);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(lean_object* v___x_164_, lean_object* v_x_165_, lean_object* v_x_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v___x_172_; 
lean_dec_ref(v___x_164_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v_x_165_);
return v___x_172_;
}
else
{
lean_object* v_key_173_; lean_object* v_value_174_; lean_object* v_tail_175_; lean_object* v___f_176_; uint8_t v___y_178_; uint8_t v___x_194_; uint8_t v___x_195_; 
v_key_173_ = lean_ctor_get(v_x_166_, 0);
lean_inc_n(v_key_173_, 2);
v_value_174_ = lean_ctor_get(v_x_166_, 1);
lean_inc(v_value_174_);
v_tail_175_ = lean_ctor_get(v_x_166_, 2);
lean_inc(v_tail_175_);
lean_dec_ref_known(v_x_166_, 3);
v___f_176_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__0));
v___x_194_ = 0;
lean_inc_ref(v___x_164_);
v___x_195_ = l_Lean_LibrarySuggestions_isDeniedPremise(v___x_164_, v_key_173_, v___x_194_);
if (v___x_195_ == 0)
{
uint8_t v___x_196_; 
lean_inc_ref(v___x_164_);
v___x_196_ = l_Lean_wasOriginallyTheorem(v___x_164_, v_key_173_);
if (v___x_196_ == 0)
{
lean_dec(v_value_174_);
v_x_166_ = v_tail_175_;
goto _start;
}
else
{
v___y_178_ = v___x_195_;
goto v___jp_177_;
}
}
else
{
lean_dec(v_key_173_);
v___y_178_ = v___x_195_;
goto v___jp_177_;
}
v___jp_177_:
{
if (v___y_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = l_Lean_ConstantInfo_type(v_value_174_);
lean_dec(v_value_174_);
v___x_180_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__4, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__4_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__4);
v___x_181_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(lean_box(0), v___f_176_, v___x_179_, v_x_165_, v___x_180_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v_fst_183_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
v_fst_183_ = lean_ctor_get(v_a_182_, 0);
lean_inc(v_fst_183_);
lean_dec(v_a_182_);
v_x_165_ = v_fst_183_;
v_x_166_ = v_tail_175_;
goto _start;
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec(v_tail_175_);
lean_dec_ref(v___x_164_);
v_a_185_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_181_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_181_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_dec(v_value_174_);
v_x_166_ = v_tail_175_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___boxed(lean_object* v___x_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_198_, v_x_199_, v_x_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(lean_object* v___x_207_, lean_object* v_as_208_, size_t v_i_209_, size_t v_stop_210_, lean_object* v_b_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = lean_usize_dec_eq(v_i_209_, v_stop_210_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_array_uget_borrowed(v_as_208_, v_i_209_);
lean_inc(v___x_218_);
lean_inc_ref(v___x_207_);
v___x_219_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_207_, v_b_211_, v___x_218_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; size_t v___x_221_; size_t v___x_222_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_a_220_);
lean_dec_ref_known(v___x_219_, 1);
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_add(v_i_209_, v___x_221_);
v_i_209_ = v___x_222_;
v_b_211_ = v_a_220_;
goto _start;
}
else
{
lean_dec_ref(v___x_207_);
return v___x_219_;
}
}
else
{
lean_object* v___x_224_; 
lean_dec_ref(v___x_207_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v_b_211_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2___boxed(lean_object* v___x_225_, lean_object* v_as_226_, lean_object* v_i_227_, lean_object* v_stop_228_, lean_object* v_b_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
size_t v_i_boxed_235_; size_t v_stop_boxed_236_; lean_object* v_res_237_; 
v_i_boxed_235_ = lean_unbox_usize(v_i_227_);
lean_dec(v_i_227_);
v_stop_boxed_236_ = lean_unbox_usize(v_stop_228_);
lean_dec(v_stop_228_);
v_res_237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_225_, v_as_226_, v_i_boxed_235_, v_stop_boxed_236_, v_b_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec_ref(v_as_226_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__0(lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v___x_243_; lean_object* v_env_244_; lean_object* v___x_245_; lean_object* v_map_u2081_246_; lean_object* v_buckets_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_243_ = lean_st_ref_get(v___y_241_);
v_env_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc_ref_n(v_env_244_, 2);
lean_dec(v___x_243_);
v___x_245_ = l_Lean_Environment_constants(v_env_244_);
v_map_u2081_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc_ref(v_map_u2081_246_);
lean_dec_ref(v___x_245_);
v_buckets_247_ = lean_ctor_get(v_map_u2081_246_, 1);
lean_inc_ref(v_buckets_247_);
lean_dec_ref(v_map_u2081_246_);
v___x_248_ = lean_box(1);
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_array_get_size(v_buckets_247_);
v___x_251_ = lean_nat_dec_lt(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec_ref(v_buckets_247_);
lean_dec_ref(v_env_244_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_248_);
return v___x_252_;
}
else
{
size_t v___x_253_; size_t v___x_254_; lean_object* v___x_255_; 
v___x_253_ = ((size_t)0ULL);
v___x_254_ = lean_usize_of_nat(v___x_250_);
v___x_255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v_env_244_, v_buckets_247_, v___x_253_, v___x_254_, v___x_248_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec_ref(v_buckets_247_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__0___boxed(lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__0(v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0(lean_object* v___y_262_, uint8_t v_isExporting_263_, lean_object* v___x_264_, lean_object* v___y_265_, lean_object* v___x_266_, lean_object* v_a_x3f_267_){
_start:
{
lean_object* v___x_269_; lean_object* v_env_270_; lean_object* v_nextMacroScope_271_; lean_object* v_ngen_272_; lean_object* v_auxDeclNGen_273_; lean_object* v_traceState_274_; lean_object* v_messages_275_; lean_object* v_infoState_276_; lean_object* v_snapshotTasks_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_302_; 
v___x_269_ = lean_st_ref_take(v___y_262_);
v_env_270_ = lean_ctor_get(v___x_269_, 0);
v_nextMacroScope_271_ = lean_ctor_get(v___x_269_, 1);
v_ngen_272_ = lean_ctor_get(v___x_269_, 2);
v_auxDeclNGen_273_ = lean_ctor_get(v___x_269_, 3);
v_traceState_274_ = lean_ctor_get(v___x_269_, 4);
v_messages_275_ = lean_ctor_get(v___x_269_, 6);
v_infoState_276_ = lean_ctor_get(v___x_269_, 7);
v_snapshotTasks_277_ = lean_ctor_get(v___x_269_, 8);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; 
v_unused_303_ = lean_ctor_get(v___x_269_, 5);
lean_dec(v_unused_303_);
v___x_279_ = v___x_269_;
v_isShared_280_ = v_isSharedCheck_302_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_snapshotTasks_277_);
lean_inc(v_infoState_276_);
lean_inc(v_messages_275_);
lean_inc(v_traceState_274_);
lean_inc(v_auxDeclNGen_273_);
lean_inc(v_ngen_272_);
lean_inc(v_nextMacroScope_271_);
lean_inc(v_env_270_);
lean_dec(v___x_269_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_302_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = l_Lean_Environment_setExporting(v_env_270_, v_isExporting_263_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 5, v___x_264_);
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_nextMacroScope_271_);
lean_ctor_set(v_reuseFailAlloc_301_, 2, v_ngen_272_);
lean_ctor_set(v_reuseFailAlloc_301_, 3, v_auxDeclNGen_273_);
lean_ctor_set(v_reuseFailAlloc_301_, 4, v_traceState_274_);
lean_ctor_set(v_reuseFailAlloc_301_, 5, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_301_, 6, v_messages_275_);
lean_ctor_set(v_reuseFailAlloc_301_, 7, v_infoState_276_);
lean_ctor_set(v_reuseFailAlloc_301_, 8, v_snapshotTasks_277_);
v___x_283_ = v_reuseFailAlloc_301_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_mctx_286_; lean_object* v_zetaDeltaFVarIds_287_; lean_object* v_postponed_288_; lean_object* v_diag_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_299_; 
v___x_284_ = lean_st_ref_put(v___y_262_, v___x_283_);
v___x_285_ = lean_st_ref_take(v___y_265_);
v_mctx_286_ = lean_ctor_get(v___x_285_, 0);
v_zetaDeltaFVarIds_287_ = lean_ctor_get(v___x_285_, 2);
v_postponed_288_ = lean_ctor_get(v___x_285_, 3);
v_diag_289_ = lean_ctor_get(v___x_285_, 4);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v___x_285_, 1);
lean_dec(v_unused_300_);
v___x_291_ = v___x_285_;
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_diag_289_);
lean_inc(v_postponed_288_);
lean_inc(v_zetaDeltaFVarIds_287_);
lean_inc(v_mctx_286_);
lean_dec(v___x_285_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_box(0);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v___x_266_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_mctx_286_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_zetaDeltaFVarIds_287_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_postponed_288_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_diag_289_);
v___x_295_ = v_reuseFailAlloc_298_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_st_ref_put(v___y_265_, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_293_);
return v___x_297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v___y_304_, lean_object* v_isExporting_305_, lean_object* v___x_306_, lean_object* v___y_307_, lean_object* v___x_308_, lean_object* v_a_x3f_309_, lean_object* v___y_310_){
_start:
{
uint8_t v_isExporting_boxed_311_; lean_object* v_res_312_; 
v_isExporting_boxed_311_ = lean_unbox(v_isExporting_305_);
v_res_312_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0(v___y_304_, v_isExporting_boxed_311_, v___x_306_, v___y_307_, v___x_308_, v_a_x3f_309_);
lean_dec(v_a_x3f_309_);
lean_dec(v___y_307_);
lean_dec(v___y_304_);
return v_res_312_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_313_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1);
v___x_319_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_ctor_set(v___x_319_, 3, v___x_318_);
lean_ctor_set(v___x_319_, 4, v___x_318_);
lean_ctor_set(v___x_319_, 5, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg(lean_object* v_x_320_, uint8_t v_isExporting_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; lean_object* v_env_328_; lean_object* v___x_329_; uint8_t v_isModule_330_; 
v___x_327_ = lean_st_ref_get(v___y_325_);
v_env_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_env_328_);
lean_dec(v___x_327_);
v___x_329_ = l_Lean_Environment_header(v_env_328_);
v_isModule_330_ = lean_ctor_get_uint8(v___x_329_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_329_);
if (v_isModule_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec_ref(v_env_328_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
v___x_331_ = lean_apply_5(v_x_320_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, lean_box(0));
return v___x_331_;
}
else
{
uint8_t v_isExporting_332_; 
v_isExporting_332_ = lean_ctor_get_uint8(v_env_328_, sizeof(void*)*8);
lean_dec_ref(v_env_328_);
if (v_isExporting_321_ == 0)
{
if (v_isExporting_332_ == 0)
{
lean_object* v___x_398_; 
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
v___x_398_ = lean_apply_5(v_x_320_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, lean_box(0));
return v___x_398_;
}
else
{
goto v___jp_333_;
}
}
else
{
if (v_isExporting_332_ == 0)
{
goto v___jp_333_;
}
else
{
lean_object* v___x_399_; 
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
v___x_399_ = lean_apply_5(v_x_320_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, lean_box(0));
return v___x_399_;
}
}
v___jp_333_:
{
lean_object* v___x_334_; lean_object* v_env_335_; lean_object* v_nextMacroScope_336_; lean_object* v_ngen_337_; lean_object* v_auxDeclNGen_338_; lean_object* v_traceState_339_; lean_object* v_messages_340_; lean_object* v_infoState_341_; lean_object* v_snapshotTasks_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_396_; 
v___x_334_ = lean_st_ref_take(v___y_325_);
v_env_335_ = lean_ctor_get(v___x_334_, 0);
v_nextMacroScope_336_ = lean_ctor_get(v___x_334_, 1);
v_ngen_337_ = lean_ctor_get(v___x_334_, 2);
v_auxDeclNGen_338_ = lean_ctor_get(v___x_334_, 3);
v_traceState_339_ = lean_ctor_get(v___x_334_, 4);
v_messages_340_ = lean_ctor_get(v___x_334_, 6);
v_infoState_341_ = lean_ctor_get(v___x_334_, 7);
v_snapshotTasks_342_ = lean_ctor_get(v___x_334_, 8);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v___x_334_, 5);
lean_dec(v_unused_397_);
v___x_344_ = v___x_334_;
v_isShared_345_ = v_isSharedCheck_396_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_snapshotTasks_342_);
lean_inc(v_infoState_341_);
lean_inc(v_messages_340_);
lean_inc(v_traceState_339_);
lean_inc(v_auxDeclNGen_338_);
lean_inc(v_ngen_337_);
lean_inc(v_nextMacroScope_336_);
lean_inc(v_env_335_);
lean_dec(v___x_334_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_396_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_346_ = l_Lean_Environment_setExporting(v_env_335_, v_isExporting_321_);
v___x_347_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__2);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 5, v___x_347_);
lean_ctor_set(v___x_344_, 0, v___x_346_);
v___x_349_ = v___x_344_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_nextMacroScope_336_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_ngen_337_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_auxDeclNGen_338_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_traceState_339_);
lean_ctor_set(v_reuseFailAlloc_395_, 5, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_395_, 6, v_messages_340_);
lean_ctor_set(v_reuseFailAlloc_395_, 7, v_infoState_341_);
lean_ctor_set(v_reuseFailAlloc_395_, 8, v_snapshotTasks_342_);
v___x_349_ = v_reuseFailAlloc_395_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_mctx_352_; lean_object* v_zetaDeltaFVarIds_353_; lean_object* v_postponed_354_; lean_object* v_diag_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_393_; 
v___x_350_ = lean_st_ref_put(v___y_325_, v___x_349_);
v___x_351_ = lean_st_ref_take(v___y_323_);
v_mctx_352_ = lean_ctor_get(v___x_351_, 0);
v_zetaDeltaFVarIds_353_ = lean_ctor_get(v___x_351_, 2);
v_postponed_354_ = lean_ctor_get(v___x_351_, 3);
v_diag_355_ = lean_ctor_get(v___x_351_, 4);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; 
v_unused_394_ = lean_ctor_get(v___x_351_, 1);
lean_dec(v_unused_394_);
v___x_357_ = v___x_351_;
v_isShared_358_ = v_isSharedCheck_393_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_diag_355_);
lean_inc(v_postponed_354_);
lean_inc(v_zetaDeltaFVarIds_353_);
lean_inc(v_mctx_352_);
lean_dec(v___x_351_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_393_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__3);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v___x_359_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_mctx_352_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_zetaDeltaFVarIds_353_);
lean_ctor_set(v_reuseFailAlloc_392_, 3, v_postponed_354_);
lean_ctor_set(v_reuseFailAlloc_392_, 4, v_diag_355_);
v___x_361_ = v_reuseFailAlloc_392_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v_r_363_; 
v___x_362_ = lean_st_ref_put(v___y_323_, v___x_361_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
v_r_363_ = lean_apply_5(v_x_320_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, lean_box(0));
if (lean_obj_tag(v_r_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_380_; 
v_a_364_ = lean_ctor_get(v_r_363_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v_r_363_);
if (v_isSharedCheck_380_ == 0)
{
v___x_366_ = v_r_363_;
v_isShared_367_ = v_isSharedCheck_380_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v_r_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_380_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
lean_inc(v_a_364_);
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 1);
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_379_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
v___x_370_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0(v___y_325_, v_isExporting_332_, v___x_347_, v___y_323_, v___x_359_, v___x_369_);
lean_dec_ref(v___x_369_);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v___x_370_, 0);
lean_dec(v_unused_378_);
v___x_372_ = v___x_370_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_dec(v___x_370_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v_a_364_);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_364_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
v_a_381_ = lean_ctor_get(v_r_363_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v_r_363_, 1);
v___x_382_ = lean_box(0);
v___x_383_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0(v___y_325_, v_isExporting_332_, v___x_347_, v___y_323_, v___x_359_, v___x_382_);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v___x_383_, 0);
lean_dec(v_unused_391_);
v___x_385_ = v___x_383_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_dec(v___x_383_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 1);
lean_ctor_set(v___x_385_, 0, v_a_381_);
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_381_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___boxed(lean_object* v_x_400_, lean_object* v_isExporting_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
uint8_t v_isExporting_boxed_407_; lean_object* v_res_408_; 
v_isExporting_boxed_407_ = lean_unbox(v_isExporting_401_);
v_res_408_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg(v_x_400_, v_isExporting_boxed_407_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg(lean_object* v_x_409_, uint8_t v_when_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
if (v_when_410_ == 0)
{
lean_object* v___x_416_; 
lean_inc(v___y_414_);
lean_inc_ref(v___y_413_);
lean_inc(v___y_412_);
lean_inc_ref(v___y_411_);
v___x_416_ = lean_apply_5(v_x_409_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, lean_box(0));
return v___x_416_;
}
else
{
uint8_t v___x_417_; lean_object* v___x_418_; 
v___x_417_ = 0;
v___x_418_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg(v_x_409_, v___x_417_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg___boxed(lean_object* v_x_419_, lean_object* v_when_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
uint8_t v_when_boxed_426_; lean_object* v_res_427_; 
v_when_boxed_426_ = lean_unbox(v_when_420_);
v_res_427_ = l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg(v_x_419_, v_when_boxed_426_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__1(lean_object* v___x_428_, lean_object* v___f_429_, uint8_t v___x_430_, lean_object* v___x_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_st_mk_ref(v___x_428_);
v___x_436_ = l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg(v___f_429_, v___x_430_, v___x_431_, v___x_435_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_445_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_445_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = lean_st_ref_get(v___x_435_);
lean_dec(v___x_435_);
lean_dec(v___x_441_);
if (v_isShared_440_ == 0)
{
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_437_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
lean_dec(v___x_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__1___boxed(lean_object* v___x_446_, lean_object* v___f_447_, lean_object* v___x_448_, lean_object* v___x_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
uint8_t v___x_5938__boxed_453_; lean_object* v_res_454_; 
v___x_5938__boxed_453_ = lean_unbox(v___x_448_);
v_res_454_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__1(v___x_446_, v___f_447_, v___x_5938__boxed_453_, v___x_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec_ref(v___x_449_);
return v_res_454_;
}
}
static uint64_t _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__2(void){
_start:
{
lean_object* v___x_462_; uint64_t v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__1));
v___x_463_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__3(void){
_start:
{
uint64_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = lean_uint64_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__2, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__2_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__2);
v___x_465_ = ((lean_object*)(l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__1));
v___x_466_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set_uint64(v___x_466_, sizeof(void*)*1, v___x_464_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__5(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_unsigned_to_nat(32u);
v___x_470_ = lean_mk_empty_array_with_capacity(v___x_469_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6(void){
_start:
{
size_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_472_ = ((size_t)5ULL);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_unsigned_to_nat(32u);
v___x_475_ = lean_mk_empty_array_with_capacity(v___x_474_);
v___x_476_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__5, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__5_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__5);
v___x_477_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
lean_ctor_set(v___x_477_, 2, v___x_473_);
lean_ctor_set(v___x_477_, 3, v___x_473_);
lean_ctor_set_usize(v___x_477_, 4, v___x_472_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__7(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_478_ = lean_box(1);
v___x_479_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6);
v___x_480_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4);
v___x_481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
lean_ctor_set(v___x_481_, 2, v___x_478_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__9(void){
_start:
{
uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_484_ = 1;
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_box(0);
v___x_487_ = ((lean_object*)(l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__8));
v___x_488_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__7, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__7_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__7);
v___x_489_ = lean_box(1);
v___x_490_ = 0;
v___x_491_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__3, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__3_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__3);
v___x_492_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_489_);
lean_ctor_set(v___x_492_, 2, v___x_488_);
lean_ctor_set(v___x_492_, 3, v___x_487_);
lean_ctor_set(v___x_492_, 4, v___x_486_);
lean_ctor_set(v___x_492_, 5, v___x_485_);
lean_ctor_set(v___x_492_, 6, v___x_486_);
lean_ctor_set_uint8(v___x_492_, sizeof(void*)*7, v___x_490_);
lean_ctor_set_uint8(v___x_492_, sizeof(void*)*7 + 1, v___x_490_);
lean_ctor_set_uint8(v___x_492_, sizeof(void*)*7 + 2, v___x_490_);
lean_ctor_set_uint8(v___x_492_, sizeof(void*)*7 + 3, v___x_484_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__10(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4);
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
lean_ctor_set(v___x_495_, 2, v___x_494_);
lean_ctor_set(v___x_495_, 3, v___x_494_);
lean_ctor_set(v___x_495_, 4, v___x_493_);
lean_ctor_set(v___x_495_, 5, v___x_493_);
lean_ctor_set(v___x_495_, 6, v___x_493_);
lean_ctor_set(v___x_495_, 7, v___x_493_);
lean_ctor_set(v___x_495_, 8, v___x_493_);
lean_ctor_set(v___x_495_, 9, v___x_493_);
lean_ctor_set(v___x_495_, 10, v___x_493_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__11(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4);
v___x_497_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
lean_ctor_set(v___x_497_, 2, v___x_496_);
lean_ctor_set(v___x_497_, 3, v___x_496_);
lean_ctor_set(v___x_497_, 4, v___x_496_);
lean_ctor_set(v___x_497_, 5, v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__12(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4);
v___x_499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
lean_ctor_set(v___x_499_, 2, v___x_498_);
lean_ctor_set(v___x_499_, 3, v___x_498_);
lean_ctor_set(v___x_499_, 4, v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__13(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_500_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__12, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__12_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__12);
v___x_501_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6);
v___x_502_ = lean_box(1);
v___x_503_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__11, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__11_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__11);
v___x_504_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__10, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__10_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__10);
v___x_505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v___x_503_);
lean_ctor_set(v___x_505_, 2, v___x_502_);
lean_ctor_set(v___x_505_, 3, v___x_501_);
lean_ctor_set(v___x_505_, 4, v___x_500_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__14(void){
_start:
{
lean_object* v___x_506_; uint8_t v___x_507_; lean_object* v___f_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___f_511_; 
v___x_506_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__9, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__9_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__9);
v___x_507_ = 1;
v___f_508_ = ((lean_object*)(l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__0));
v___x_509_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__13, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__13_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__13);
v___x_510_ = lean_box(v___x_507_);
v___f_511_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__1___boxed), 7, 4);
lean_closure_set(v___f_511_, 0, v___x_509_);
lean_closure_set(v___f_511_, 1, v___f_508_);
lean_closure_set(v___f_511_, 2, v___x_510_);
lean_closure_set(v___f_511_, 3, v___x_506_);
return v___f_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap(lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef;
v___x_516_ = lean_st_ref_get(v___x_515_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v___f_517_; lean_object* v___x_518_; 
v___f_517_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__14, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__14_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__14);
v___x_518_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg(v___f_517_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_528_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_528_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
lean_inc(v_a_519_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v_a_519_);
v___x_524_ = lean_st_ref_swap(v___x_515_, v___x_523_);
lean_dec(v___x_524_);
if (v_isShared_522_ == 0)
{
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_519_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
else
{
return v___x_518_;
}
}
else
{
lean_object* v_val_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
v_val_529_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_516_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_val_529_);
lean_dec(v___x_516_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set_tag(v___x_531_, 0);
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_val_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___boxed(lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_LibrarySuggestions_symbolFrequencyMap(v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0(lean_object* v_k_541_, lean_object* v_t_542_, lean_object* v_hl_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg(v_k_541_, v_t_542_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3(lean_object* v_00_u03b1_545_, lean_object* v_x_546_, uint8_t v_isExporting_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg(v_x_546_, v_isExporting_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___boxed(lean_object* v_00_u03b1_554_, lean_object* v_x_555_, lean_object* v_isExporting_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v_isExporting_boxed_562_; lean_object* v_res_563_; 
v_isExporting_boxed_562_ = lean_unbox(v_isExporting_556_);
v_res_563_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3(v_00_u03b1_554_, v_x_555_, v_isExporting_boxed_562_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3(lean_object* v_00_u03b1_564_, lean_object* v_x_565_, uint8_t v_when_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg(v_x_565_, v_when_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___boxed(lean_object* v_00_u03b1_573_, lean_object* v_x_574_, lean_object* v_when_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v_when_boxed_581_; lean_object* v_res_582_; 
v_when_boxed_581_ = lean_unbox(v_when_575_);
v_res_582_ = l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3(v_00_u03b1_573_, v_x_574_, v_when_boxed_581_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg(lean_object* v_t_583_, lean_object* v_k_584_, lean_object* v_fallback_585_){
_start:
{
if (lean_obj_tag(v_t_583_) == 0)
{
lean_object* v_k_586_; lean_object* v_v_587_; lean_object* v_l_588_; lean_object* v_r_589_; uint8_t v___x_590_; 
v_k_586_ = lean_ctor_get(v_t_583_, 1);
v_v_587_ = lean_ctor_get(v_t_583_, 2);
v_l_588_ = lean_ctor_get(v_t_583_, 3);
v_r_589_ = lean_ctor_get(v_t_583_, 4);
v___x_590_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_584_, v_k_586_);
switch(v___x_590_)
{
case 0:
{
v_t_583_ = v_l_588_;
goto _start;
}
case 1:
{
lean_inc(v_v_587_);
return v_v_587_;
}
default: 
{
v_t_583_ = v_r_589_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_585_);
return v_fallback_585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg___boxed(lean_object* v_t_593_, lean_object* v_k_594_, lean_object* v_fallback_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg(v_t_593_, v_k_594_, v_fallback_595_);
lean_dec(v_fallback_595_);
lean_dec(v_k_594_);
lean_dec(v_t_593_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency(lean_object* v_n_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_LibrarySuggestions_symbolFrequencyMap(v_a_598_, v_a_599_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_611_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_611_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_611_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg(v_a_602_, v_n_597_, v___x_606_);
lean_dec(v_a_602_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_607_);
v___x_609_ = v___x_604_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
v_a_612_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_601_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_601_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___boxed(lean_object* v_n_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_LibrarySuggestions_symbolFrequency(v_n_620_, v_a_621_, v_a_622_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_n_620_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0(lean_object* v_00_u03b4_625_, lean_object* v_t_626_, lean_object* v_k_627_, lean_object* v_fallback_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg(v_t_626_, v_k_627_, v_fallback_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___boxed(lean_object* v_00_u03b4_630_, lean_object* v_t_631_, lean_object* v_k_632_, lean_object* v_fallback_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0(v_00_u03b4_630_, v_t_631_, v_k_632_, v_fallback_633_);
lean_dec(v_fallback_633_);
lean_dec(v_k_632_);
lean_dec(v_t_631_);
return v_res_634_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_SymbolFrequency_1332954629____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LibrarySuggestions_SymbolFrequency(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LibrarySuggestions_SymbolFrequency(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
}
#ifdef __cplusplus
}
#endif
