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
lean_object* v___x_23_; lean_object* v_toCold_24_; lean_object* v_currRecDepth_25_; lean_object* v_ref_26_; uint16_t v_optionFlags_27_; uint8_t v_suppressElabErrors_28_; uint8_t v_isRecordingDeps_29_; lean_object* v_fileName_30_; lean_object* v_fileMap_31_; lean_object* v_options_32_; lean_object* v_maxRecDepth_33_; lean_object* v_currNamespace_34_; lean_object* v_openDecls_35_; lean_object* v_initHeartbeats_36_; lean_object* v_quotContext_37_; lean_object* v_currMacroScope_38_; lean_object* v_cancelTk_x3f_39_; lean_object* v_inheritedTraceOptions_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec_ref_known(v___x_22_, 1);
v___x_23_ = lean_io_get_num_heartbeats();
v_toCold_24_ = lean_ctor_get(v_a_18_, 0);
v_currRecDepth_25_ = lean_ctor_get(v_a_18_, 1);
v_ref_26_ = lean_ctor_get(v_a_18_, 2);
v_optionFlags_27_ = lean_ctor_get_uint16(v_a_18_, sizeof(void*)*3);
v_suppressElabErrors_28_ = lean_ctor_get_uint8(v_a_18_, sizeof(void*)*3 + 2);
v_isRecordingDeps_29_ = lean_ctor_get_uint8(v_a_18_, sizeof(void*)*3 + 3);
v_fileName_30_ = lean_ctor_get(v_toCold_24_, 0);
v_fileMap_31_ = lean_ctor_get(v_toCold_24_, 1);
v_options_32_ = lean_ctor_get(v_toCold_24_, 2);
v_maxRecDepth_33_ = lean_ctor_get(v_toCold_24_, 3);
v_currNamespace_34_ = lean_ctor_get(v_toCold_24_, 4);
v_openDecls_35_ = lean_ctor_get(v_toCold_24_, 5);
v_initHeartbeats_36_ = lean_ctor_get(v_toCold_24_, 6);
v_quotContext_37_ = lean_ctor_get(v_toCold_24_, 8);
v_currMacroScope_38_ = lean_ctor_get(v_toCold_24_, 9);
v_cancelTk_x3f_39_ = lean_ctor_get(v_toCold_24_, 10);
v_inheritedTraceOptions_40_ = lean_ctor_get(v_toCold_24_, 11);
v___x_41_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inheritedTraceOptions_40_);
lean_inc(v_cancelTk_x3f_39_);
lean_inc(v_currMacroScope_38_);
lean_inc(v_quotContext_37_);
lean_inc(v_initHeartbeats_36_);
lean_inc(v_openDecls_35_);
lean_inc(v_currNamespace_34_);
lean_inc(v_maxRecDepth_33_);
lean_inc_ref(v_options_32_);
lean_inc_ref(v_fileMap_31_);
lean_inc_ref(v_fileName_30_);
v___x_42_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_42_, 0, v_fileName_30_);
lean_ctor_set(v___x_42_, 1, v_fileMap_31_);
lean_ctor_set(v___x_42_, 2, v_options_32_);
lean_ctor_set(v___x_42_, 3, v_maxRecDepth_33_);
lean_ctor_set(v___x_42_, 4, v_currNamespace_34_);
lean_ctor_set(v___x_42_, 5, v_openDecls_35_);
lean_ctor_set(v___x_42_, 6, v_initHeartbeats_36_);
lean_ctor_set(v___x_42_, 7, v___x_41_);
lean_ctor_set(v___x_42_, 8, v_quotContext_37_);
lean_ctor_set(v___x_42_, 9, v_currMacroScope_38_);
lean_ctor_set(v___x_42_, 10, v_cancelTk_x3f_39_);
lean_ctor_set(v___x_42_, 11, v_inheritedTraceOptions_40_);
lean_inc(v_ref_26_);
lean_inc(v_currRecDepth_25_);
v___x_43_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v_currRecDepth_25_);
lean_ctor_set(v___x_43_, 2, v_ref_26_);
lean_ctor_set_uint16(v___x_43_, sizeof(void*)*3, v_optionFlags_27_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*3 + 2, v_suppressElabErrors_28_);
lean_ctor_set_uint8(v___x_43_, sizeof(void*)*3 + 3, v_isRecordingDeps_29_);
lean_inc(v_a_19_);
v___x_44_ = lean_apply_3(v_x_17_, v___x_43_, v_a_19_, lean_box(0));
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_61_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_61_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_61_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_61_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
lean_inc(v_a_45_);
if (v_isShared_48_ == 0)
{
lean_ctor_set_tag(v___x_47_, 1);
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_60_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
v___x_51_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___lam__0(v___x_23_, v___x_50_);
lean_dec_ref(v___x_50_);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_58_ == 0)
{
lean_object* v_unused_59_; 
v_unused_59_ = lean_ctor_get(v___x_51_, 0);
lean_dec(v_unused_59_);
v___x_53_ = v___x_51_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_dec(v___x_51_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v_a_45_);
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_45_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
v_a_62_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_a_62_);
lean_dec_ref_known(v___x_44_, 1);
v___x_63_ = lean_box(0);
v___x_64_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___lam__0(v___x_23_, v___x_63_);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v___x_64_, 0);
lean_dec(v_unused_72_);
v___x_66_ = v___x_64_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_dec(v___x_64_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
lean_ctor_set_tag(v___x_66_, 1);
lean_ctor_set(v___x_66_, 0, v_a_62_);
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_a_62_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
lean_dec_ref(v_x_17_);
v_a_73_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_22_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_22_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg___boxed(lean_object* v_x_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg(v_x_81_, v_a_82_, v_a_83_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats(lean_object* v_00_u03b1_86_, lean_object* v_x_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg(v_x_87_, v_a_88_, v_a_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___boxed(lean_object* v_00_u03b1_92_, lean_object* v_x_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats(v_00_u03b1_92_, v_x_93_, v_a_94_, v_a_95_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0(lean_object* v_count_98_){
_start:
{
lean_object* v___y_100_; 
if (lean_obj_tag(v_count_98_) == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v___y_100_ = v___x_104_;
goto v___jp_99_;
}
else
{
lean_object* v_val_105_; 
v_val_105_ = lean_ctor_get(v_count_98_, 0);
v___y_100_ = v_val_105_;
goto v___jp_99_;
}
v___jp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v___y_100_, v___x_101_);
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0___boxed(lean_object* v_count_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0(v_count_106_);
lean_dec(v_count_106_);
return v_res_107_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_box(0);
v___x_109_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0(v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg(lean_object* v_k_110_, lean_object* v_t_111_){
_start:
{
if (lean_obj_tag(v_t_111_) == 0)
{
lean_object* v_size_112_; lean_object* v_k_113_; lean_object* v_v_114_; lean_object* v_l_115_; lean_object* v_r_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_131_; 
v_size_112_ = lean_ctor_get(v_t_111_, 0);
v_k_113_ = lean_ctor_get(v_t_111_, 1);
v_v_114_ = lean_ctor_get(v_t_111_, 2);
v_l_115_ = lean_ctor_get(v_t_111_, 3);
v_r_116_ = lean_ctor_get(v_t_111_, 4);
v_isSharedCheck_131_ = !lean_is_exclusive(v_t_111_);
if (v_isSharedCheck_131_ == 0)
{
v___x_118_ = v_t_111_;
v_isShared_119_ = v_isSharedCheck_131_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_r_116_);
lean_inc(v_l_115_);
lean_inc(v_v_114_);
lean_inc(v_k_113_);
lean_inc(v_size_112_);
lean_dec(v_t_111_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_131_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
uint8_t v___x_120_; 
v___x_120_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_110_, v_k_113_);
switch(v___x_120_)
{
case 0:
{
lean_object* v_impl_121_; lean_object* v___x_122_; 
lean_del_object(v___x_118_);
lean_dec(v_size_112_);
v_impl_121_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg(v_k_110_, v_l_115_);
v___x_122_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_113_, v_v_114_, v_impl_121_, v_r_116_);
return v___x_122_;
}
case 1:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_val_125_; lean_object* v___x_127_; 
lean_dec(v_k_113_);
v___x_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_123_, 0, v_v_114_);
v___x_124_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___lam__0(v___x_123_);
lean_dec_ref_known(v___x_123_, 1);
v_val_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_val_125_);
lean_dec(v___x_124_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 2, v_val_125_);
lean_ctor_set(v___x_118_, 1, v_k_110_);
v___x_127_ = v___x_118_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_size_112_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_k_110_);
lean_ctor_set(v_reuseFailAlloc_128_, 2, v_val_125_);
lean_ctor_set(v_reuseFailAlloc_128_, 3, v_l_115_);
lean_ctor_set(v_reuseFailAlloc_128_, 4, v_r_116_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
default: 
{
lean_object* v_impl_129_; lean_object* v___x_130_; 
lean_del_object(v___x_118_);
lean_dec(v_size_112_);
v_impl_129_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg(v_k_110_, v_r_116_);
v___x_130_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_113_, v_v_114_, v_l_115_, v_impl_129_);
return v___x_130_;
}
}
}
}
else
{
lean_object* v___x_132_; lean_object* v_val_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_132_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg___closed__0);
v_val_133_ = lean_ctor_get(v___x_132_, 0);
v___x_134_ = lean_unsigned_to_nat(1u);
lean_inc(v_val_133_);
v___x_135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_k_110_);
lean_ctor_set(v___x_135_, 2, v_val_133_);
lean_ctor_set(v___x_135_, 3, v_t_111_);
lean_ctor_set(v___x_135_, 4, v_t_111_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___lam__0(lean_object* v_n_136_, lean_object* v_acc_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg(v_n_136_, v_acc_137_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___lam__0___boxed(lean_object* v_n_145_, lean_object* v_acc_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___lam__0(v_n_145_, v_acc_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_152_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__1(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(64u);
v___x_155_ = l_Lean_mkPtrSet___redArg(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__2(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_box(0);
v___x_157_ = lean_unsigned_to_nat(16u);
v___x_158_ = lean_mk_array(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__3(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__2, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__2_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__2);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__4(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__3, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__3);
v___x_163_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__1, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__1_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__1);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(lean_object* v___x_165_, lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_object* v___x_173_; 
lean_dec_ref(v___x_165_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v_x_166_);
return v___x_173_;
}
else
{
lean_object* v_key_174_; lean_object* v_value_175_; lean_object* v_tail_176_; lean_object* v___f_177_; uint8_t v___y_179_; uint8_t v___x_195_; uint8_t v___x_196_; 
v_key_174_ = lean_ctor_get(v_x_167_, 0);
lean_inc_n(v_key_174_, 2);
v_value_175_ = lean_ctor_get(v_x_167_, 1);
lean_inc(v_value_175_);
v_tail_176_ = lean_ctor_get(v_x_167_, 2);
lean_inc(v_tail_176_);
lean_dec_ref_known(v_x_167_, 3);
v___f_177_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__0));
v___x_195_ = 0;
lean_inc_ref(v___x_165_);
v___x_196_ = l_Lean_LibrarySuggestions_isDeniedPremise(v___x_165_, v_key_174_, v___x_195_);
if (v___x_196_ == 0)
{
uint8_t v___x_197_; 
lean_inc_ref(v___x_165_);
v___x_197_ = l_Lean_wasOriginallyTheorem(v___x_165_, v_key_174_);
if (v___x_197_ == 0)
{
lean_dec(v_value_175_);
v_x_167_ = v_tail_176_;
goto _start;
}
else
{
v___y_179_ = v___x_196_;
goto v___jp_178_;
}
}
else
{
lean_dec(v_key_174_);
v___y_179_ = v___x_196_;
goto v___jp_178_;
}
v___jp_178_:
{
if (v___y_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = l_Lean_ConstantInfo_type(v_value_175_);
lean_dec(v_value_175_);
v___x_181_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__4, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__4_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___closed__4);
v___x_182_ = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(lean_box(0), v___f_177_, v___x_180_, v_x_166_, v___x_181_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v_fst_184_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
v_fst_184_ = lean_ctor_get(v_a_183_, 0);
lean_inc(v_fst_184_);
lean_dec(v_a_183_);
v_x_166_ = v_fst_184_;
v_x_167_ = v_tail_176_;
goto _start;
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec(v_tail_176_);
lean_dec_ref(v___x_165_);
v_a_186_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_182_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_182_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_dec(v_value_175_);
v_x_167_ = v_tail_176_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1___boxed(lean_object* v___x_199_, lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_199_, v_x_200_, v_x_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(lean_object* v___x_208_, lean_object* v_as_209_, size_t v_i_210_, size_t v_stop_211_, lean_object* v_b_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = lean_usize_dec_eq(v_i_210_, v_stop_211_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_array_uget_borrowed(v_as_209_, v_i_210_);
lean_inc(v___x_219_);
lean_inc_ref(v___x_208_);
v___x_220_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__1(v___x_208_, v_b_212_, v___x_219_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; size_t v___x_222_; size_t v___x_223_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_add(v_i_210_, v___x_222_);
v_i_210_ = v___x_223_;
v_b_212_ = v_a_221_;
goto _start;
}
else
{
lean_dec_ref(v___x_208_);
return v___x_220_;
}
}
else
{
lean_object* v___x_225_; 
lean_dec_ref(v___x_208_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v_b_212_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2___boxed(lean_object* v___x_226_, lean_object* v_as_227_, lean_object* v_i_228_, lean_object* v_stop_229_, lean_object* v_b_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
size_t v_i_boxed_236_; size_t v_stop_boxed_237_; lean_object* v_res_238_; 
v_i_boxed_236_ = lean_unbox_usize(v_i_228_);
lean_dec(v_i_228_);
v_stop_boxed_237_ = lean_unbox_usize(v_stop_229_);
lean_dec(v_stop_229_);
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v___x_226_, v_as_227_, v_i_boxed_236_, v_stop_boxed_237_, v_b_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec_ref(v_as_227_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__0(lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; lean_object* v_env_245_; lean_object* v___x_246_; lean_object* v_map_u2081_247_; lean_object* v_buckets_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_244_ = lean_st_ref_get(v___y_242_);
v_env_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc_ref_n(v_env_245_, 2);
lean_dec(v___x_244_);
v___x_246_ = l_Lean_Environment_constants(v_env_245_);
v_map_u2081_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc_ref(v_map_u2081_247_);
lean_dec_ref(v___x_246_);
v_buckets_248_ = lean_ctor_get(v_map_u2081_247_, 1);
lean_inc_ref(v_buckets_248_);
lean_dec_ref(v_map_u2081_247_);
v___x_249_ = lean_box(1);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_array_get_size(v_buckets_248_);
v___x_252_ = lean_nat_dec_lt(v___x_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec_ref(v_buckets_248_);
lean_dec_ref(v_env_245_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_249_);
return v___x_253_;
}
else
{
size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; 
v___x_254_ = ((size_t)0ULL);
v___x_255_ = lean_usize_of_nat(v___x_251_);
v___x_256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__2(v_env_245_, v_buckets_248_, v___x_254_, v___x_255_, v___x_249_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec_ref(v_buckets_248_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__0___boxed(lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__0(v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0(lean_object* v___y_263_, uint8_t v_isExporting_264_, lean_object* v___x_265_, lean_object* v___y_266_, lean_object* v___x_267_, lean_object* v_a_x3f_268_){
_start:
{
lean_object* v___x_270_; lean_object* v_env_271_; lean_object* v_nextMacroScope_272_; lean_object* v_ngen_273_; lean_object* v_auxDeclNGen_274_; lean_object* v_traceState_275_; lean_object* v_recordedDeps_276_; lean_object* v_messages_277_; lean_object* v_infoState_278_; lean_object* v_snapshotTasks_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_304_; 
v___x_270_ = lean_st_ref_take(v___y_263_);
v_env_271_ = lean_ctor_get(v___x_270_, 0);
v_nextMacroScope_272_ = lean_ctor_get(v___x_270_, 1);
v_ngen_273_ = lean_ctor_get(v___x_270_, 2);
v_auxDeclNGen_274_ = lean_ctor_get(v___x_270_, 3);
v_traceState_275_ = lean_ctor_get(v___x_270_, 4);
v_recordedDeps_276_ = lean_ctor_get(v___x_270_, 6);
v_messages_277_ = lean_ctor_get(v___x_270_, 7);
v_infoState_278_ = lean_ctor_get(v___x_270_, 8);
v_snapshotTasks_279_ = lean_ctor_get(v___x_270_, 9);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v___x_270_, 5);
lean_dec(v_unused_305_);
v___x_281_ = v___x_270_;
v_isShared_282_ = v_isSharedCheck_304_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_snapshotTasks_279_);
lean_inc(v_infoState_278_);
lean_inc(v_messages_277_);
lean_inc(v_recordedDeps_276_);
lean_inc(v_traceState_275_);
lean_inc(v_auxDeclNGen_274_);
lean_inc(v_ngen_273_);
lean_inc(v_nextMacroScope_272_);
lean_inc(v_env_271_);
lean_dec(v___x_270_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_304_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = l_Lean_Environment_setExporting(v_env_271_, v_isExporting_264_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 5, v___x_265_);
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_nextMacroScope_272_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_ngen_273_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_auxDeclNGen_274_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_traceState_275_);
lean_ctor_set(v_reuseFailAlloc_303_, 5, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_303_, 6, v_recordedDeps_276_);
lean_ctor_set(v_reuseFailAlloc_303_, 7, v_messages_277_);
lean_ctor_set(v_reuseFailAlloc_303_, 8, v_infoState_278_);
lean_ctor_set(v_reuseFailAlloc_303_, 9, v_snapshotTasks_279_);
v___x_285_ = v_reuseFailAlloc_303_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_mctx_288_; lean_object* v_zetaDeltaFVarIds_289_; lean_object* v_postponed_290_; lean_object* v_diag_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_301_; 
v___x_286_ = lean_st_ref_put(v___y_263_, v___x_285_);
v___x_287_ = lean_st_ref_take(v___y_266_);
v_mctx_288_ = lean_ctor_get(v___x_287_, 0);
v_zetaDeltaFVarIds_289_ = lean_ctor_get(v___x_287_, 2);
v_postponed_290_ = lean_ctor_get(v___x_287_, 3);
v_diag_291_ = lean_ctor_get(v___x_287_, 4);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v___x_287_, 1);
lean_dec(v_unused_302_);
v___x_293_ = v___x_287_;
v_isShared_294_ = v_isSharedCheck_301_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_diag_291_);
lean_inc(v_postponed_290_);
lean_inc(v_zetaDeltaFVarIds_289_);
lean_inc(v_mctx_288_);
lean_dec(v___x_287_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_301_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_box(0);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_267_);
v___x_297_ = v___x_293_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_mctx_288_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_300_, 2, v_zetaDeltaFVarIds_289_);
lean_ctor_set(v_reuseFailAlloc_300_, 3, v_postponed_290_);
lean_ctor_set(v_reuseFailAlloc_300_, 4, v_diag_291_);
v___x_297_ = v_reuseFailAlloc_300_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_st_ref_put(v___y_266_, v___x_297_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_295_);
return v___x_299_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v___y_306_, lean_object* v_isExporting_307_, lean_object* v___x_308_, lean_object* v___y_309_, lean_object* v___x_310_, lean_object* v_a_x3f_311_, lean_object* v___y_312_){
_start:
{
uint8_t v_isExporting_boxed_313_; lean_object* v_res_314_; 
v_isExporting_boxed_313_ = lean_unbox(v_isExporting_307_);
v_res_314_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0(v___y_306_, v_isExporting_boxed_313_, v___x_308_, v___y_309_, v___x_310_, v_a_x3f_311_);
lean_dec(v_a_x3f_311_);
lean_dec(v___y_309_);
lean_dec(v___y_306_);
return v_res_314_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_315_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__1);
v___x_321_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
lean_ctor_set(v___x_321_, 3, v___x_320_);
lean_ctor_set(v___x_321_, 4, v___x_320_);
lean_ctor_set(v___x_321_, 5, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg(lean_object* v_x_322_, uint8_t v_isExporting_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; lean_object* v_env_330_; lean_object* v___x_331_; uint8_t v_isModule_332_; 
v___x_329_ = lean_st_ref_get(v___y_327_);
v_env_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_env_330_);
lean_dec(v___x_329_);
v___x_331_ = l_Lean_Environment_header(v_env_330_);
v_isModule_332_ = lean_ctor_get_uint8(v___x_331_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_331_);
if (v_isModule_332_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v_env_330_);
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
v___x_333_ = lean_apply_5(v_x_322_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, lean_box(0));
return v___x_333_;
}
else
{
uint8_t v_isExporting_334_; 
v_isExporting_334_ = lean_ctor_get_uint8(v_env_330_, sizeof(void*)*8);
lean_dec_ref(v_env_330_);
if (v_isExporting_323_ == 0)
{
if (v_isExporting_334_ == 0)
{
lean_object* v___x_401_; 
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
v___x_401_ = lean_apply_5(v_x_322_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, lean_box(0));
return v___x_401_;
}
else
{
goto v___jp_335_;
}
}
else
{
if (v_isExporting_334_ == 0)
{
goto v___jp_335_;
}
else
{
lean_object* v___x_402_; 
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
v___x_402_ = lean_apply_5(v_x_322_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, lean_box(0));
return v___x_402_;
}
}
v___jp_335_:
{
lean_object* v___x_336_; lean_object* v_env_337_; lean_object* v_nextMacroScope_338_; lean_object* v_ngen_339_; lean_object* v_auxDeclNGen_340_; lean_object* v_traceState_341_; lean_object* v_recordedDeps_342_; lean_object* v_messages_343_; lean_object* v_infoState_344_; lean_object* v_snapshotTasks_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_399_; 
v___x_336_ = lean_st_ref_take(v___y_327_);
v_env_337_ = lean_ctor_get(v___x_336_, 0);
v_nextMacroScope_338_ = lean_ctor_get(v___x_336_, 1);
v_ngen_339_ = lean_ctor_get(v___x_336_, 2);
v_auxDeclNGen_340_ = lean_ctor_get(v___x_336_, 3);
v_traceState_341_ = lean_ctor_get(v___x_336_, 4);
v_recordedDeps_342_ = lean_ctor_get(v___x_336_, 6);
v_messages_343_ = lean_ctor_get(v___x_336_, 7);
v_infoState_344_ = lean_ctor_get(v___x_336_, 8);
v_snapshotTasks_345_ = lean_ctor_get(v___x_336_, 9);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v___x_336_, 5);
lean_dec(v_unused_400_);
v___x_347_ = v___x_336_;
v_isShared_348_ = v_isSharedCheck_399_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snapshotTasks_345_);
lean_inc(v_infoState_344_);
lean_inc(v_messages_343_);
lean_inc(v_recordedDeps_342_);
lean_inc(v_traceState_341_);
lean_inc(v_auxDeclNGen_340_);
lean_inc(v_ngen_339_);
lean_inc(v_nextMacroScope_338_);
lean_inc(v_env_337_);
lean_dec(v___x_336_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_399_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_349_ = l_Lean_Environment_setExporting(v_env_337_, v_isExporting_323_);
v___x_350_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__2);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 5, v___x_350_);
lean_ctor_set(v___x_347_, 0, v___x_349_);
v___x_352_ = v___x_347_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_nextMacroScope_338_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_ngen_339_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_auxDeclNGen_340_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_traceState_341_);
lean_ctor_set(v_reuseFailAlloc_398_, 5, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_398_, 6, v_recordedDeps_342_);
lean_ctor_set(v_reuseFailAlloc_398_, 7, v_messages_343_);
lean_ctor_set(v_reuseFailAlloc_398_, 8, v_infoState_344_);
lean_ctor_set(v_reuseFailAlloc_398_, 9, v_snapshotTasks_345_);
v___x_352_ = v_reuseFailAlloc_398_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_mctx_355_; lean_object* v_zetaDeltaFVarIds_356_; lean_object* v_postponed_357_; lean_object* v_diag_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_396_; 
v___x_353_ = lean_st_ref_put(v___y_327_, v___x_352_);
v___x_354_ = lean_st_ref_take(v___y_325_);
v_mctx_355_ = lean_ctor_get(v___x_354_, 0);
v_zetaDeltaFVarIds_356_ = lean_ctor_get(v___x_354_, 2);
v_postponed_357_ = lean_ctor_get(v___x_354_, 3);
v_diag_358_ = lean_ctor_get(v___x_354_, 4);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v___x_354_, 1);
lean_dec(v_unused_397_);
v___x_360_ = v___x_354_;
v_isShared_361_ = v_isSharedCheck_396_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_diag_358_);
lean_inc(v_postponed_357_);
lean_inc(v_zetaDeltaFVarIds_356_);
lean_inc(v_mctx_355_);
lean_dec(v___x_354_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_396_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__3);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_mctx_355_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_zetaDeltaFVarIds_356_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_postponed_357_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_diag_358_);
v___x_364_ = v_reuseFailAlloc_395_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v_r_366_; 
v___x_365_ = lean_st_ref_put(v___y_325_, v___x_364_);
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
v_r_366_ = lean_apply_5(v_x_322_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, lean_box(0));
if (lean_obj_tag(v_r_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_383_; 
v_a_367_ = lean_ctor_get(v_r_366_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_r_366_);
if (v_isSharedCheck_383_ == 0)
{
v___x_369_ = v_r_366_;
v_isShared_370_ = v_isSharedCheck_383_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v_r_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_383_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
lean_inc(v_a_367_);
if (v_isShared_370_ == 0)
{
lean_ctor_set_tag(v___x_369_, 1);
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_382_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
v___x_373_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0(v___y_327_, v_isExporting_334_, v___x_350_, v___y_325_, v___x_362_, v___x_372_);
lean_dec_ref(v___x_372_);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v___x_373_, 0);
lean_dec(v_unused_381_);
v___x_375_ = v___x_373_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_dec(v___x_373_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v_a_367_);
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_367_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_a_384_ = lean_ctor_get(v_r_366_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v_r_366_, 1);
v___x_385_ = lean_box(0);
v___x_386_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___lam__0(v___y_327_, v_isExporting_334_, v___x_350_, v___y_325_, v___x_362_, v___x_385_);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; 
v_unused_394_ = lean_ctor_get(v___x_386_, 0);
lean_dec(v_unused_394_);
v___x_388_ = v___x_386_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_dec(v___x_386_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set_tag(v___x_388_, 1);
lean_ctor_set(v___x_388_, 0, v_a_384_);
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_384_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___boxed(lean_object* v_x_403_, lean_object* v_isExporting_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
uint8_t v_isExporting_boxed_410_; lean_object* v_res_411_; 
v_isExporting_boxed_410_ = lean_unbox(v_isExporting_404_);
v_res_411_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg(v_x_403_, v_isExporting_boxed_410_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg(lean_object* v_x_412_, uint8_t v_when_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
if (v_when_413_ == 0)
{
lean_object* v___x_419_; 
lean_inc(v___y_417_);
lean_inc_ref(v___y_416_);
lean_inc(v___y_415_);
lean_inc_ref(v___y_414_);
v___x_419_ = lean_apply_5(v_x_412_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, lean_box(0));
return v___x_419_;
}
else
{
uint8_t v___x_420_; lean_object* v___x_421_; 
v___x_420_ = 0;
v___x_421_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg(v_x_412_, v___x_420_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg___boxed(lean_object* v_x_422_, lean_object* v_when_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
uint8_t v_when_boxed_429_; lean_object* v_res_430_; 
v_when_boxed_429_ = lean_unbox(v_when_423_);
v_res_430_ = l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg(v_x_422_, v_when_boxed_429_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__1(lean_object* v___x_431_, lean_object* v___f_432_, uint8_t v___x_433_, lean_object* v___x_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_st_mk_ref(v___x_431_);
v___x_439_ = l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg(v___f_432_, v___x_433_, v___x_434_, v___x_438_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_448_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_st_ref_get(v___x_438_);
lean_dec(v___x_438_);
lean_dec(v___x_444_);
if (v_isShared_443_ == 0)
{
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_440_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
else
{
lean_dec(v___x_438_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__1___boxed(lean_object* v___x_449_, lean_object* v___f_450_, lean_object* v___x_451_, lean_object* v___x_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
uint8_t v___x_5971__boxed_456_; lean_object* v_res_457_; 
v___x_5971__boxed_456_ = lean_unbox(v___x_451_);
v_res_457_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__1(v___x_449_, v___f_450_, v___x_5971__boxed_456_, v___x_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec_ref(v___x_452_);
return v_res_457_;
}
}
static uint64_t _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__2(void){
_start:
{
lean_object* v___x_465_; uint64_t v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__1));
v___x_466_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__3(void){
_start:
{
uint64_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = lean_uint64_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__2, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__2_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__2);
v___x_468_ = ((lean_object*)(l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__1));
v___x_469_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set_uint64(v___x_469_, sizeof(void*)*1, v___x_467_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg___closed__0);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__5(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_unsigned_to_nat(32u);
v___x_473_ = lean_mk_empty_array_with_capacity(v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6(void){
_start:
{
size_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_475_ = ((size_t)5ULL);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_unsigned_to_nat(32u);
v___x_478_ = lean_mk_empty_array_with_capacity(v___x_477_);
v___x_479_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__5, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__5_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__5);
v___x_480_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_478_);
lean_ctor_set(v___x_480_, 2, v___x_476_);
lean_ctor_set(v___x_480_, 3, v___x_476_);
lean_ctor_set_usize(v___x_480_, 4, v___x_475_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__7(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_481_ = lean_box(1);
v___x_482_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6);
v___x_483_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4);
v___x_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_482_);
lean_ctor_set(v___x_484_, 2, v___x_481_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__9(void){
_start:
{
uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_487_ = 1;
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = lean_box(0);
v___x_490_ = ((lean_object*)(l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__8));
v___x_491_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__7, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__7_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__7);
v___x_492_ = lean_box(1);
v___x_493_ = 0;
v___x_494_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__3, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__3_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__3);
v___x_495_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_492_);
lean_ctor_set(v___x_495_, 2, v___x_491_);
lean_ctor_set(v___x_495_, 3, v___x_490_);
lean_ctor_set(v___x_495_, 4, v___x_489_);
lean_ctor_set(v___x_495_, 5, v___x_488_);
lean_ctor_set(v___x_495_, 6, v___x_489_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7, v___x_493_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7 + 1, v___x_493_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7 + 2, v___x_493_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*7 + 3, v___x_487_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__10(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
lean_ctor_set(v___x_498_, 2, v___x_497_);
lean_ctor_set(v___x_498_, 3, v___x_497_);
lean_ctor_set(v___x_498_, 4, v___x_496_);
lean_ctor_set(v___x_498_, 5, v___x_496_);
lean_ctor_set(v___x_498_, 6, v___x_496_);
lean_ctor_set(v___x_498_, 7, v___x_496_);
lean_ctor_set(v___x_498_, 8, v___x_496_);
lean_ctor_set(v___x_498_, 9, v___x_496_);
lean_ctor_set(v___x_498_, 10, v___x_496_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__11(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4);
v___x_500_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
lean_ctor_set(v___x_500_, 2, v___x_499_);
lean_ctor_set(v___x_500_, 3, v___x_499_);
lean_ctor_set(v___x_500_, 4, v___x_499_);
lean_ctor_set(v___x_500_, 5, v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__12(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__4);
v___x_502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
lean_ctor_set(v___x_502_, 2, v___x_501_);
lean_ctor_set(v___x_502_, 3, v___x_501_);
lean_ctor_set(v___x_502_, 4, v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__13(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_503_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__12, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__12_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__12);
v___x_504_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__6);
v___x_505_ = lean_box(1);
v___x_506_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__11, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__11_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__11);
v___x_507_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__10, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__10_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__10);
v___x_508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v___x_506_);
lean_ctor_set(v___x_508_, 2, v___x_505_);
lean_ctor_set(v___x_508_, 3, v___x_504_);
lean_ctor_set(v___x_508_, 4, v___x_503_);
return v___x_508_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__14(void){
_start:
{
lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v___f_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___f_514_; 
v___x_509_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__9, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__9_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__9);
v___x_510_ = 1;
v___f_511_ = ((lean_object*)(l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__0));
v___x_512_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__13, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__13_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__13);
v___x_513_ = lean_box(v___x_510_);
v___f_514_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_symbolFrequencyMap___lam__1___boxed), 7, 4);
lean_closure_set(v___f_514_, 0, v___x_512_);
lean_closure_set(v___f_514_, 1, v___f_511_);
lean_closure_set(v___f_514_, 2, v___x_513_);
lean_closure_set(v___f_514_, 3, v___x_509_);
return v___f_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap(lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_symbolFrequencyMapRef;
v___x_519_ = lean_st_ref_get(v___x_518_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___f_520_; lean_object* v___x_521_; 
v___f_520_ = lean_obj_once(&l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__14, &l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__14_once, _init_l_Lean_LibrarySuggestions_symbolFrequencyMap___closed__14);
v___x_521_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_LibrarySuggestions_withUncountedHeartbeats___redArg(v___f_520_, v_a_515_, v_a_516_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_531_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_531_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_531_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
lean_inc(v_a_522_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v_a_522_);
v___x_527_ = lean_st_ref_swap(v___x_518_, v___x_526_);
lean_dec(v___x_527_);
if (v_isShared_525_ == 0)
{
v___x_529_ = v___x_524_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_522_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
return v___x_521_;
}
}
else
{
lean_object* v_val_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_val_532_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_519_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_val_532_);
lean_dec(v___x_519_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set_tag(v___x_534_, 0);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_val_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___boxed(lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_LibrarySuggestions_symbolFrequencyMap(v_a_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0(lean_object* v_k_544_, lean_object* v_t_545_, lean_object* v_hl_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__0___redArg(v_k_544_, v_t_545_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3(lean_object* v_00_u03b1_548_, lean_object* v_x_549_, uint8_t v_isExporting_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___redArg(v_x_549_, v_isExporting_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3___boxed(lean_object* v_00_u03b1_557_, lean_object* v_x_558_, lean_object* v_isExporting_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
uint8_t v_isExporting_boxed_565_; lean_object* v_res_566_; 
v_isExporting_boxed_565_ = lean_unbox(v_isExporting_559_);
v_res_566_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3_spec__3(v_00_u03b1_557_, v_x_558_, v_isExporting_boxed_565_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3(lean_object* v_00_u03b1_567_, lean_object* v_x_568_, uint8_t v_when_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___redArg(v_x_568_, v_when_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3___boxed(lean_object* v_00_u03b1_576_, lean_object* v_x_577_, lean_object* v_when_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
uint8_t v_when_boxed_584_; lean_object* v_res_585_; 
v_when_boxed_584_ = lean_unbox(v_when_578_);
v_res_585_ = l_Lean_withoutExporting___at___00Lean_LibrarySuggestions_symbolFrequencyMap_spec__3(v_00_u03b1_576_, v_x_577_, v_when_boxed_584_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg(lean_object* v_t_586_, lean_object* v_k_587_, lean_object* v_fallback_588_){
_start:
{
if (lean_obj_tag(v_t_586_) == 0)
{
lean_object* v_k_589_; lean_object* v_v_590_; lean_object* v_l_591_; lean_object* v_r_592_; uint8_t v___x_593_; 
v_k_589_ = lean_ctor_get(v_t_586_, 1);
v_v_590_ = lean_ctor_get(v_t_586_, 2);
v_l_591_ = lean_ctor_get(v_t_586_, 3);
v_r_592_ = lean_ctor_get(v_t_586_, 4);
v___x_593_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_587_, v_k_589_);
switch(v___x_593_)
{
case 0:
{
v_t_586_ = v_l_591_;
goto _start;
}
case 1:
{
lean_inc(v_v_590_);
return v_v_590_;
}
default: 
{
v_t_586_ = v_r_592_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_588_);
return v_fallback_588_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg___boxed(lean_object* v_t_596_, lean_object* v_k_597_, lean_object* v_fallback_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg(v_t_596_, v_k_597_, v_fallback_598_);
lean_dec(v_fallback_598_);
lean_dec(v_k_597_);
lean_dec(v_t_596_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency(lean_object* v_n_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_LibrarySuggestions_symbolFrequencyMap(v_a_601_, v_a_602_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_614_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_614_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_614_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg(v_a_605_, v_n_600_, v___x_609_);
lean_dec(v_a_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_610_);
v___x_612_ = v___x_607_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_604_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_604_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_symbolFrequency___boxed(lean_object* v_n_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_LibrarySuggestions_symbolFrequency(v_n_623_, v_a_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_n_623_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0(lean_object* v_00_u03b4_628_, lean_object* v_t_629_, lean_object* v_k_630_, lean_object* v_fallback_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___redArg(v_t_629_, v_k_630_, v_fallback_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0___boxed(lean_object* v_00_u03b4_633_, lean_object* v_t_634_, lean_object* v_k_635_, lean_object* v_fallback_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_symbolFrequency_spec__0(v_00_u03b4_633_, v_t_634_, v_k_635_, v_fallback_636_);
lean_dec(v_fallback_636_);
lean_dec(v_k_635_);
lean_dec(v_t_634_);
return v_res_637_;
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
