// Lean compiler output
// Module: Lean.Data.RBTree
// Imports: public import Lean.Data.RBMap
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
lean_object* l_Lean_RBNode_findCore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_min___redArg(lean_object*);
lean_object* l_Lean_RBNode_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_RBNode_isRed___redArg(lean_object*);
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_RBNode_revFold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t l_Lean_RBNode_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_depth___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_fold___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isBlack___redArg(lean_object*);
lean_object* l_Lean_RBNode_balLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBMap_filter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_RBNode_all___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_max___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBTree___redArg();
LEAN_EXPORT lean_object* l_Lean_mkRBTree___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBTree___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___redArg();
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_RBTree_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_empty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_depth(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBTree_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_RBTree_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBTree_toList___redArg___closed__0 = (const lean_object*)&l_Lean_RBTree_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_RBTree_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_RBTree_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_RBTree_toArray___redArg___closed__0 = (const lean_object*)&l_Lean_RBTree_toArray___redArg___closed__0_value;
static const lean_array_object l_Lean_RBTree_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_RBTree_toArray___redArg___closed__1 = (const lean_object*)&l_Lean_RBTree_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_min(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_min___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_max(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_max___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_RBTree_instRepr___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.rbtreeOf "};
static const lean_object* l_Lean_RBTree_instRepr___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_RBTree_instRepr___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_RBTree_instRepr___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_RBTree_instRepr___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_RBTree_instRepr___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_RBTree_instRepr___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_erase___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_erase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_contains(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_all___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_subset___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_subset(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_seteq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_seteq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_union___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_union(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_diff___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_diff(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBTree_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rbtreeOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rbtreeOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_instInhabitedRBTree___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree(lean_object* v_00_u03b1_5_, lean_object* v_p_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___boxed(lean_object* v_00_u03b1_8_, lean_object* v_p_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_instInhabitedRBTree(v_00_u03b1_8_, v_p_9_);
lean_dec_ref(v_p_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBTree___redArg(){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBTree___redArg___boxed(lean_object* v___dummy_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_mkRBTree___redArg();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBTree(lean_object* v_00_u03b1_15_, lean_object* v_cmp_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_box(0);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBTree___boxed(lean_object* v_00_u03b1_18_, lean_object* v_cmp_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_mkRBTree(v_00_u03b1_18_, v_cmp_19_);
lean_dec_ref(v_cmp_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___redArg(){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_box(0);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___redArg___boxed(lean_object* v___dummy_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_instEmptyCollectionRBTree___redArg();
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree(lean_object* v_00_u03b1_25_, lean_object* v_cmp_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(0);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___boxed(lean_object* v_00_u03b1_28_, lean_object* v_cmp_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instEmptyCollectionRBTree(v_00_u03b1_28_, v_cmp_29_);
lean_dec_ref(v_cmp_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_empty___redArg(){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(0);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_empty___redArg___boxed(lean_object* v___dummy_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_RBTree_empty___redArg();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_empty(lean_object* v_00_u03b1_35_, lean_object* v_cmp_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(0);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_empty___boxed(lean_object* v_00_u03b1_38_, lean_object* v_cmp_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_RBTree_empty(v_00_u03b1_38_, v_cmp_39_);
lean_dec_ref(v_cmp_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg(lean_object* v_f_41_, lean_object* v_t_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_RBNode_depth___redArg(v_f_41_, v_t_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg___boxed(lean_object* v_f_44_, lean_object* v_t_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_RBTree_depth___redArg(v_f_44_, v_t_45_);
lean_dec(v_t_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth(lean_object* v_00_u03b1_47_, lean_object* v_cmp_48_, lean_object* v_f_49_, lean_object* v_t_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_RBNode_depth___redArg(v_f_49_, v_t_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___boxed(lean_object* v_00_u03b1_52_, lean_object* v_cmp_53_, lean_object* v_f_54_, lean_object* v_t_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_RBTree_depth(v_00_u03b1_52_, v_cmp_53_, v_f_54_, v_t_55_);
lean_dec(v_t_55_);
lean_dec_ref(v_cmp_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg___lam__0(lean_object* v_f_57_, lean_object* v_r_58_, lean_object* v_a_59_, lean_object* v_x_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_apply_2(v_f_57_, v_r_58_, v_a_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg(lean_object* v_f_62_, lean_object* v_init_63_, lean_object* v_t_64_){
_start:
{
lean_object* v___f_65_; lean_object* v___x_66_; 
v___f_65_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_65_, 0, v_f_62_);
v___x_66_ = l_Lean_RBNode_fold___redArg(v___f_65_, v_init_63_, v_t_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold(lean_object* v_00_u03b1_67_, lean_object* v_00_u03b2_68_, lean_object* v_cmp_69_, lean_object* v_f_70_, lean_object* v_init_71_, lean_object* v_t_72_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; 
v___f_73_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_73_, 0, v_f_70_);
v___x_74_ = l_Lean_RBNode_fold___redArg(v___f_73_, v_init_71_, v_t_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___boxed(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_cmp_77_, lean_object* v_f_78_, lean_object* v_init_79_, lean_object* v_t_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_RBTree_fold(v_00_u03b1_75_, v_00_u03b2_76_, v_cmp_77_, v_f_78_, v_init_79_, v_t_80_);
lean_dec_ref(v_cmp_77_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___redArg(lean_object* v_f_82_, lean_object* v_init_83_, lean_object* v_t_84_){
_start:
{
lean_object* v___f_85_; lean_object* v___x_86_; 
v___f_85_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_85_, 0, v_f_82_);
v___x_86_ = l_Lean_RBNode_revFold___redArg(v___f_85_, v_init_83_, v_t_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_cmp_89_, lean_object* v_f_90_, lean_object* v_init_91_, lean_object* v_t_92_){
_start:
{
lean_object* v___f_93_; lean_object* v___x_94_; 
v___f_93_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_93_, 0, v_f_90_);
v___x_94_ = l_Lean_RBNode_revFold___redArg(v___f_93_, v_init_91_, v_t_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___boxed(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_cmp_97_, lean_object* v_f_98_, lean_object* v_init_99_, lean_object* v_t_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_RBTree_revFold(v_00_u03b1_95_, v_00_u03b2_96_, v_cmp_97_, v_f_98_, v_init_99_, v_t_100_);
lean_dec_ref(v_cmp_97_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___redArg(lean_object* v_inst_102_, lean_object* v_f_103_, lean_object* v_init_104_, lean_object* v_t_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; 
v___f_106_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_106_, 0, v_f_103_);
v___x_107_ = l_Lean_RBNode_foldM___redArg(v_inst_102_, v___f_106_, v_init_104_, v_t_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_cmp_110_, lean_object* v_m_111_, lean_object* v_inst_112_, lean_object* v_f_113_, lean_object* v_init_114_, lean_object* v_t_115_){
_start:
{
lean_object* v___f_116_; lean_object* v___x_117_; 
v___f_116_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_116_, 0, v_f_113_);
v___x_117_ = l_Lean_RBNode_foldM___redArg(v_inst_112_, v___f_116_, v_init_114_, v_t_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___boxed(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_cmp_120_, lean_object* v_m_121_, lean_object* v_inst_122_, lean_object* v_f_123_, lean_object* v_init_124_, lean_object* v_t_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_RBTree_foldM(v_00_u03b1_118_, v_00_u03b2_119_, v_cmp_120_, v_m_121_, v_inst_122_, v_f_123_, v_init_124_, v_t_125_);
lean_dec_ref(v_cmp_120_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg___lam__0(lean_object* v_f_127_, lean_object* v_r_128_, lean_object* v_a_129_, lean_object* v_x_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_apply_1(v_f_127_, v_a_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg(lean_object* v_inst_132_, lean_object* v_f_133_, lean_object* v_t_134_){
_start:
{
lean_object* v___f_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___f_135_ = lean_alloc_closure((void*)(l_Lean_RBTree_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_135_, 0, v_f_133_);
v___x_136_ = lean_box(0);
v___x_137_ = l_Lean_RBNode_foldM___redArg(v_inst_132_, v___f_135_, v___x_136_, v_t_134_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM(lean_object* v_00_u03b1_138_, lean_object* v_cmp_139_, lean_object* v_m_140_, lean_object* v_inst_141_, lean_object* v_f_142_, lean_object* v_t_143_){
_start:
{
lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___f_144_ = lean_alloc_closure((void*)(l_Lean_RBTree_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_144_, 0, v_f_142_);
v___x_145_ = lean_box(0);
v___x_146_ = l_Lean_RBNode_foldM___redArg(v_inst_141_, v___f_144_, v___x_145_, v_t_143_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___boxed(lean_object* v_00_u03b1_147_, lean_object* v_cmp_148_, lean_object* v_m_149_, lean_object* v_inst_150_, lean_object* v_f_151_, lean_object* v_t_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_RBTree_forM(v_00_u03b1_147_, v_cmp_148_, v_m_149_, v_inst_150_, v_f_151_, v_t_152_);
lean_dec_ref(v_cmp_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__0(lean_object* v_f_154_, lean_object* v_a_155_, lean_object* v_x_156_, lean_object* v_acc_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lean_apply_2(v_f_154_, v_a_155_, v_acc_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__1(lean_object* v_toPure_159_, lean_object* v_____do__lift_160_){
_start:
{
lean_object* v_a_161_; lean_object* v___x_162_; 
v_a_161_ = lean_ctor_get(v_____do__lift_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref(v_____do__lift_160_);
v___x_162_ = lean_apply_2(v_toPure_159_, lean_box(0), v_a_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg(lean_object* v_inst_163_, lean_object* v_t_164_, lean_object* v_init_165_, lean_object* v_f_166_){
_start:
{
lean_object* v_toApplicative_167_; lean_object* v_toBind_168_; lean_object* v_toPure_169_; lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___x_173_; 
v_toApplicative_167_ = lean_ctor_get(v_inst_163_, 0);
v_toBind_168_ = lean_ctor_get(v_inst_163_, 1);
lean_inc(v_toBind_168_);
v_toPure_169_ = lean_ctor_get(v_toApplicative_167_, 1);
lean_inc(v_toPure_169_);
v___f_170_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_170_, 0, v_f_166_);
v___x_171_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_163_, v___f_170_, v_t_164_, v_init_165_);
v___f_172_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_172_, 0, v_toPure_169_);
v___x_173_ = lean_apply_4(v_toBind_168_, lean_box(0), lean_box(0), v___x_171_, v___f_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn(lean_object* v_00_u03b1_174_, lean_object* v_cmp_175_, lean_object* v_m_176_, lean_object* v_00_u03c3_177_, lean_object* v_inst_178_, lean_object* v_t_179_, lean_object* v_init_180_, lean_object* v_f_181_){
_start:
{
lean_object* v_toApplicative_182_; lean_object* v_toBind_183_; lean_object* v_toPure_184_; lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v___f_187_; lean_object* v___x_188_; 
v_toApplicative_182_ = lean_ctor_get(v_inst_178_, 0);
v_toBind_183_ = lean_ctor_get(v_inst_178_, 1);
lean_inc(v_toBind_183_);
v_toPure_184_ = lean_ctor_get(v_toApplicative_182_, 1);
lean_inc(v_toPure_184_);
v___f_185_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_185_, 0, v_f_181_);
v___x_186_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_178_, v___f_185_, v_t_179_, v_init_180_);
v___f_187_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_187_, 0, v_toPure_184_);
v___x_188_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___x_186_, v___f_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___boxed(lean_object* v_00_u03b1_189_, lean_object* v_cmp_190_, lean_object* v_m_191_, lean_object* v_00_u03c3_192_, lean_object* v_inst_193_, lean_object* v_t_194_, lean_object* v_init_195_, lean_object* v_f_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_RBTree_forIn(v_00_u03b1_189_, v_cmp_190_, v_m_191_, v_00_u03c3_192_, v_inst_193_, v_t_194_, v_init_195_, v_f_196_);
lean_dec_ref(v_cmp_190_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__0(lean_object* v___y_198_, lean_object* v_a_199_, lean_object* v_x_200_, lean_object* v_acc_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_apply_2(v___y_198_, v_a_199_, v_acc_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__2(lean_object* v_inst_203_, lean_object* v_00_u03b2_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_toApplicative_208_; lean_object* v_toBind_209_; lean_object* v_toPure_210_; lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___f_213_; lean_object* v___x_214_; 
v_toApplicative_208_ = lean_ctor_get(v_inst_203_, 0);
v_toBind_209_ = lean_ctor_get(v_inst_203_, 1);
lean_inc(v_toBind_209_);
v_toPure_210_ = lean_ctor_get(v_toApplicative_208_, 1);
lean_inc(v_toPure_210_);
v___f_211_ = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_211_, 0, v___y_207_);
v___x_212_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_203_, v___f_211_, v___y_205_, v___y_206_);
v___f_213_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_213_, 0, v_toPure_210_);
v___x_214_ = lean_apply_4(v_toBind_209_, lean_box(0), lean_box(0), v___x_212_, v___f_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg(lean_object* v_inst_215_){
_start:
{
lean_object* v___f_216_; 
v___f_216_ = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_216_, 0, v_inst_215_);
return v___f_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad(lean_object* v_00_u03b1_217_, lean_object* v_cmp_218_, lean_object* v_m_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v___f_221_; 
v___f_221_ = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_221_, 0, v_inst_220_);
return v___f_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___boxed(lean_object* v_00_u03b1_222_, lean_object* v_cmp_223_, lean_object* v_m_224_, lean_object* v_inst_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_RBTree_instForInOfMonad(v_00_u03b1_222_, v_cmp_223_, v_m_224_, v_inst_225_);
lean_dec_ref(v_cmp_223_);
return v_res_226_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_isEmpty___redArg(lean_object* v_t_227_){
_start:
{
if (lean_obj_tag(v_t_227_) == 0)
{
uint8_t v___x_228_; 
v___x_228_ = 1;
return v___x_228_;
}
else
{
uint8_t v___x_229_; 
v___x_229_ = 0;
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___redArg___boxed(lean_object* v_t_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Lean_RBTree_isEmpty___redArg(v_t_230_);
lean_dec(v_t_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_isEmpty(lean_object* v_00_u03b1_233_, lean_object* v_cmp_234_, lean_object* v_t_235_){
_start:
{
if (lean_obj_tag(v_t_235_) == 0)
{
uint8_t v___x_236_; 
v___x_236_ = 1;
return v___x_236_;
}
else
{
uint8_t v___x_237_; 
v___x_237_ = 0;
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___boxed(lean_object* v_00_u03b1_238_, lean_object* v_cmp_239_, lean_object* v_t_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Lean_RBTree_isEmpty(v_00_u03b1_238_, v_cmp_239_, v_t_240_);
lean_dec(v_t_240_);
lean_dec_ref(v_cmp_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg___lam__0(lean_object* v_r_243_, lean_object* v_a_244_, lean_object* v_x_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_246_, 0, v_a_244_);
lean_ctor_set(v___x_246_, 1, v_r_243_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg(lean_object* v_t_248_){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___f_249_ = ((lean_object*)(l_Lean_RBTree_toList___redArg___closed__0));
v___x_250_ = lean_box(0);
v___x_251_ = l_Lean_RBNode_revFold___redArg(v___f_249_, v___x_250_, v_t_248_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList(lean_object* v_00_u03b1_252_, lean_object* v_cmp_253_, lean_object* v_t_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_RBTree_toList___redArg(v_t_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___boxed(lean_object* v_00_u03b1_256_, lean_object* v_cmp_257_, lean_object* v_t_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_RBTree_toList(v_00_u03b1_256_, v_cmp_257_, v_t_258_);
lean_dec_ref(v_cmp_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg___lam__0(lean_object* v_r_260_, lean_object* v_a_261_, lean_object* v_x_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_array_push(v_r_260_, v_a_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg(lean_object* v_t_267_){
_start:
{
lean_object* v___f_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___f_268_ = ((lean_object*)(l_Lean_RBTree_toArray___redArg___closed__0));
v___x_269_ = ((lean_object*)(l_Lean_RBTree_toArray___redArg___closed__1));
v___x_270_ = l_Lean_RBNode_fold___redArg(v___f_268_, v___x_269_, v_t_267_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray(lean_object* v_00_u03b1_271_, lean_object* v_cmp_272_, lean_object* v_t_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_RBTree_toArray___redArg(v_t_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___boxed(lean_object* v_00_u03b1_275_, lean_object* v_cmp_276_, lean_object* v_t_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_RBTree_toArray(v_00_u03b1_275_, v_cmp_276_, v_t_277_);
lean_dec_ref(v_cmp_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg(lean_object* v_t_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_RBNode_min___redArg(v_t_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; 
v___x_281_ = lean_box(0);
return v___x_281_;
}
else
{
lean_object* v_val_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_290_; 
v_val_282_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_290_ == 0)
{
v___x_284_ = v___x_280_;
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_val_282_);
lean_dec(v___x_280_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_fst_286_; lean_object* v___x_288_; 
v_fst_286_ = lean_ctor_get(v_val_282_, 0);
lean_inc(v_fst_286_);
lean_dec(v_val_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v_fst_286_);
v___x_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_fst_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg___boxed(lean_object* v_t_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_RBTree_min___redArg(v_t_291_);
lean_dec(v_t_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min(lean_object* v_00_u03b1_293_, lean_object* v_cmp_294_, lean_object* v_t_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_RBNode_min___redArg(v_t_295_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_box(0);
return v___x_297_;
}
else
{
lean_object* v_val_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_306_; 
v_val_298_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_306_ == 0)
{
v___x_300_ = v___x_296_;
v_isShared_301_ = v_isSharedCheck_306_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_val_298_);
lean_dec(v___x_296_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_306_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_fst_302_; lean_object* v___x_304_; 
v_fst_302_ = lean_ctor_get(v_val_298_, 0);
lean_inc(v_fst_302_);
lean_dec(v_val_298_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v_fst_302_);
v___x_304_ = v___x_300_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_fst_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min___boxed(lean_object* v_00_u03b1_307_, lean_object* v_cmp_308_, lean_object* v_t_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_RBTree_min(v_00_u03b1_307_, v_cmp_308_, v_t_309_);
lean_dec(v_t_309_);
lean_dec_ref(v_cmp_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg(lean_object* v_t_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_RBNode_max___redArg(v_t_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_box(0);
return v___x_313_;
}
else
{
lean_object* v_val_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_322_; 
v_val_314_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_322_ == 0)
{
v___x_316_ = v___x_312_;
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_val_314_);
lean_dec(v___x_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_322_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_fst_318_; lean_object* v___x_320_; 
v_fst_318_ = lean_ctor_get(v_val_314_, 0);
lean_inc(v_fst_318_);
lean_dec(v_val_314_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 0, v_fst_318_);
v___x_320_ = v___x_316_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_fst_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg___boxed(lean_object* v_t_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_RBTree_max___redArg(v_t_323_);
lean_dec(v_t_323_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max(lean_object* v_00_u03b1_325_, lean_object* v_cmp_326_, lean_object* v_t_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_RBNode_max___redArg(v_t_327_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_box(0);
return v___x_329_;
}
else
{
lean_object* v_val_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_338_; 
v_val_330_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_338_ == 0)
{
v___x_332_ = v___x_328_;
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_val_330_);
lean_dec(v___x_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_338_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_fst_334_; lean_object* v___x_336_; 
v_fst_334_ = lean_ctor_get(v_val_330_, 0);
lean_inc(v_fst_334_);
lean_dec(v_val_330_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v_fst_334_);
v___x_336_ = v___x_332_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_fst_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max___boxed(lean_object* v_00_u03b1_339_, lean_object* v_cmp_340_, lean_object* v_t_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_RBTree_max(v_00_u03b1_339_, v_cmp_340_, v_t_341_);
lean_dec(v_t_341_);
lean_dec_ref(v_cmp_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0(lean_object* v_inst_346_, lean_object* v_t_347_, lean_object* v_prec_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_349_ = ((lean_object*)(l_Lean_RBTree_instRepr___redArg___lam__0___closed__1));
v___x_350_ = l_Lean_RBTree_toList___redArg(v_t_347_);
v___x_351_ = l_List_repr___redArg(v_inst_346_, v___x_350_);
v___x_352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_349_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = l_Repr_addAppParen(v___x_352_, v_prec_348_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0___boxed(lean_object* v_inst_354_, lean_object* v_t_355_, lean_object* v_prec_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_RBTree_instRepr___redArg___lam__0(v_inst_354_, v_t_355_, v_prec_356_);
lean_dec(v_prec_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg(lean_object* v_inst_358_){
_start:
{
lean_object* v___f_359_; 
v___f_359_ = lean_alloc_closure((void*)(l_Lean_RBTree_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_359_, 0, v_inst_358_);
return v___f_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr(lean_object* v_00_u03b1_360_, lean_object* v_cmp_361_, lean_object* v_inst_362_){
_start:
{
lean_object* v___f_363_; 
v___f_363_ = lean_alloc_closure((void*)(l_Lean_RBTree_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_363_, 0, v_inst_362_);
return v___f_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___boxed(lean_object* v_00_u03b1_364_, lean_object* v_cmp_365_, lean_object* v_inst_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_RBTree_instRepr(v_00_u03b1_364_, v_cmp_365_, v_inst_366_);
lean_dec_ref(v_cmp_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_insert___redArg(lean_object* v_cmp_368_, lean_object* v_t_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_box(0);
v___x_372_ = l_Lean_RBNode_insert___redArg(v_cmp_368_, v_t_369_, v_a_370_, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_insert(lean_object* v_00_u03b1_373_, lean_object* v_cmp_374_, lean_object* v_t_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_box(0);
v___x_378_ = l_Lean_RBNode_insert___redArg(v_cmp_374_, v_t_375_, v_a_376_, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_erase___redArg(lean_object* v_cmp_379_, lean_object* v_t_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_RBNode_erase___redArg(v_cmp_379_, v_a_381_, v_t_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_erase(lean_object* v_00_u03b1_383_, lean_object* v_cmp_384_, lean_object* v_t_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_RBNode_erase___redArg(v_cmp_384_, v_a_386_, v_t_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___redArg(lean_object* v_cmp_388_, lean_object* v_x_389_){
_start:
{
if (lean_obj_tag(v_x_389_) == 0)
{
lean_object* v___x_390_; 
lean_dec_ref(v_cmp_388_);
v___x_390_ = lean_box(0);
return v___x_390_;
}
else
{
lean_object* v_head_391_; lean_object* v_tail_392_; lean_object* v_val_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_head_391_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_head_391_);
v_tail_392_ = lean_ctor_get(v_x_389_, 1);
lean_inc(v_tail_392_);
lean_dec_ref_known(v_x_389_, 2);
lean_inc_ref(v_cmp_388_);
v_val_393_ = l_Lean_RBTree_ofList___redArg(v_cmp_388_, v_tail_392_);
v___x_394_ = lean_box(0);
v___x_395_ = l_Lean_RBNode_insert___redArg(v_cmp_388_, v_val_393_, v_head_391_, v___x_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList(lean_object* v_00_u03b1_396_, lean_object* v_cmp_397_, lean_object* v_x_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_RBTree_ofList___redArg(v_cmp_397_, v_x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f___redArg(lean_object* v_cmp_400_, lean_object* v_t_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_RBNode_findCore___redArg(v_cmp_400_, v_t_401_, v_a_402_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_404_; 
v___x_404_ = lean_box(0);
return v___x_404_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
v_val_405_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_413_ == 0)
{
v___x_407_ = v___x_403_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_val_405_);
lean_dec(v___x_403_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_fst_409_; lean_object* v___x_411_; 
v_fst_409_ = lean_ctor_get(v_val_405_, 0);
lean_inc(v_fst_409_);
lean_dec(v_val_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v_fst_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_fst_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f(lean_object* v_00_u03b1_414_, lean_object* v_cmp_415_, lean_object* v_t_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_RBNode_findCore___redArg(v_cmp_415_, v_t_416_, v_a_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_419_; 
v___x_419_ = lean_box(0);
return v___x_419_;
}
else
{
lean_object* v_val_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_428_; 
v_val_420_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_428_ == 0)
{
v___x_422_ = v___x_418_;
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_val_420_);
lean_dec(v___x_418_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_428_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_fst_424_; lean_object* v___x_426_; 
v_fst_424_ = lean_ctor_get(v_val_420_, 0);
lean_inc(v_fst_424_);
lean_dec(v_val_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v_fst_424_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_fst_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_contains___redArg(lean_object* v_cmp_429_, lean_object* v_t_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_RBNode_findCore___redArg(v_cmp_429_, v_t_430_, v_a_431_);
if (lean_obj_tag(v___x_432_) == 0)
{
uint8_t v___x_433_; 
v___x_433_ = 0;
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
lean_dec_ref_known(v___x_432_, 1);
v___x_434_ = 1;
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___redArg___boxed(lean_object* v_cmp_435_, lean_object* v_t_436_, lean_object* v_a_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Lean_RBTree_contains___redArg(v_cmp_435_, v_t_436_, v_a_437_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_contains(lean_object* v_00_u03b1_440_, lean_object* v_cmp_441_, lean_object* v_t_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_RBNode_findCore___redArg(v_cmp_441_, v_t_442_, v_a_443_);
if (lean_obj_tag(v___x_444_) == 0)
{
uint8_t v___x_445_; 
v___x_445_ = 0;
return v___x_445_;
}
else
{
uint8_t v___x_446_; 
lean_dec_ref_known(v___x_444_, 1);
v___x_446_ = 1;
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___boxed(lean_object* v_00_u03b1_447_, lean_object* v_cmp_448_, lean_object* v_t_449_, lean_object* v_a_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_Lean_RBTree_contains(v_00_u03b1_447_, v_cmp_448_, v_t_449_, v_a_450_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(lean_object* v_cmp_453_, lean_object* v_x_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
uint8_t v___x_457_; lean_object* v___x_458_; 
lean_dec_ref(v_cmp_453_);
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_458_, 0, v_x_454_);
lean_ctor_set(v___x_458_, 1, v_x_455_);
lean_ctor_set(v___x_458_, 2, v_x_456_);
lean_ctor_set(v___x_458_, 3, v_x_454_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*4, v___x_457_);
return v___x_458_;
}
else
{
uint8_t v_color_459_; 
v_color_459_ = lean_ctor_get_uint8(v_x_454_, sizeof(void*)*4);
if (v_color_459_ == 0)
{
lean_object* v_lchild_460_; lean_object* v_key_461_; lean_object* v_val_462_; lean_object* v_rchild_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_480_; 
v_lchild_460_ = lean_ctor_get(v_x_454_, 0);
v_key_461_ = lean_ctor_get(v_x_454_, 1);
v_val_462_ = lean_ctor_get(v_x_454_, 2);
v_rchild_463_ = lean_ctor_get(v_x_454_, 3);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_454_);
if (v_isSharedCheck_480_ == 0)
{
v___x_465_ = v_x_454_;
v_isShared_466_ = v_isSharedCheck_480_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_rchild_463_);
lean_inc(v_val_462_);
lean_inc(v_key_461_);
lean_inc(v_lchild_460_);
lean_dec(v_x_454_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_480_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; uint8_t v___x_468_; 
lean_inc_ref(v_cmp_453_);
lean_inc(v_key_461_);
lean_inc(v_x_455_);
v___x_467_ = lean_apply_2(v_cmp_453_, v_x_455_, v_key_461_);
v___x_468_ = lean_unbox(v___x_467_);
switch(v___x_468_)
{
case 0:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_453_, v_lchild_460_, v_x_455_, v_x_456_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_469_);
v___x_471_ = v___x_465_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_key_461_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v_val_462_);
lean_ctor_set(v_reuseFailAlloc_472_, 3, v_rchild_463_);
lean_ctor_set_uint8(v_reuseFailAlloc_472_, sizeof(void*)*4, v_color_459_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
case 1:
{
lean_object* v___x_474_; 
lean_dec(v_val_462_);
lean_dec(v_key_461_);
lean_dec_ref(v_cmp_453_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 2, v_x_456_);
lean_ctor_set(v___x_465_, 1, v_x_455_);
v___x_474_ = v___x_465_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_lchild_460_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_x_455_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_x_456_);
lean_ctor_set(v_reuseFailAlloc_475_, 3, v_rchild_463_);
lean_ctor_set_uint8(v_reuseFailAlloc_475_, sizeof(void*)*4, v_color_459_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
default: 
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_453_, v_rchild_463_, v_x_455_, v_x_456_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 3, v___x_476_);
v___x_478_ = v___x_465_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_lchild_460_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_key_461_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_val_462_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v___x_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_479_, sizeof(void*)*4, v_color_459_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_object* v_lchild_481_; lean_object* v_key_482_; lean_object* v_val_483_; lean_object* v_rchild_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_643_; 
v_lchild_481_ = lean_ctor_get(v_x_454_, 0);
v_key_482_ = lean_ctor_get(v_x_454_, 1);
v_val_483_ = lean_ctor_get(v_x_454_, 2);
v_rchild_484_ = lean_ctor_get(v_x_454_, 3);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_454_);
if (v_isSharedCheck_643_ == 0)
{
v___x_486_ = v_x_454_;
v_isShared_487_ = v_isSharedCheck_643_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_rchild_484_);
lean_inc(v_val_483_);
lean_inc(v_key_482_);
lean_inc(v_lchild_481_);
lean_dec(v_x_454_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_643_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; uint8_t v___x_489_; 
lean_inc_ref(v_cmp_453_);
lean_inc(v_key_482_);
lean_inc(v_x_455_);
v___x_488_ = lean_apply_2(v_cmp_453_, v_x_455_, v_key_482_);
v___x_489_ = lean_unbox(v___x_488_);
switch(v___x_489_)
{
case 0:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_453_, v_lchild_481_, v_x_455_, v_x_456_);
if (lean_obj_tag(v___x_490_) == 1)
{
uint8_t v_color_491_; lean_object* v_lchild_492_; lean_object* v_key_493_; lean_object* v_val_494_; lean_object* v_rchild_495_; lean_object* v_a_497_; lean_object* v_kx_498_; lean_object* v_vx_499_; lean_object* v_b_500_; lean_object* v_ky_501_; lean_object* v_vy_502_; lean_object* v_c_503_; lean_object* v_kz_504_; lean_object* v_vz_505_; lean_object* v_d_506_; 
v_color_491_ = lean_ctor_get_uint8(v___x_490_, sizeof(void*)*4);
v_lchild_492_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_lchild_492_);
v_key_493_ = lean_ctor_get(v___x_490_, 1);
lean_inc(v_key_493_);
v_val_494_ = lean_ctor_get(v___x_490_, 2);
lean_inc(v_val_494_);
v_rchild_495_ = lean_ctor_get(v___x_490_, 3);
lean_inc(v_rchild_495_);
if (v_color_491_ == 0)
{
if (lean_obj_tag(v_lchild_492_) == 1)
{
uint8_t v_color_512_; 
v_color_512_ = lean_ctor_get_uint8(v_lchild_492_, sizeof(void*)*4);
if (v_color_512_ == 0)
{
lean_object* v_lchild_513_; lean_object* v_key_514_; lean_object* v_val_515_; lean_object* v_rchild_516_; 
lean_dec_ref_known(v___x_490_, 4);
v_lchild_513_ = lean_ctor_get(v_lchild_492_, 0);
lean_inc(v_lchild_513_);
v_key_514_ = lean_ctor_get(v_lchild_492_, 1);
lean_inc(v_key_514_);
v_val_515_ = lean_ctor_get(v_lchild_492_, 2);
lean_inc(v_val_515_);
v_rchild_516_ = lean_ctor_get(v_lchild_492_, 3);
lean_inc(v_rchild_516_);
lean_dec_ref_known(v_lchild_492_, 4);
v_a_497_ = v_lchild_513_;
v_kx_498_ = v_key_514_;
v_vx_499_ = v_val_515_;
v_b_500_ = v_rchild_516_;
v_ky_501_ = v_key_493_;
v_vy_502_ = v_val_494_;
v_c_503_ = v_rchild_495_;
v_kz_504_ = v_key_482_;
v_vz_505_ = v_val_483_;
v_d_506_ = v_rchild_484_;
goto v___jp_496_;
}
else
{
if (lean_obj_tag(v_rchild_495_) == 1)
{
uint8_t v_color_517_; 
v_color_517_ = lean_ctor_get_uint8(v_rchild_495_, sizeof(void*)*4);
if (v_color_517_ == 0)
{
lean_object* v_lchild_518_; lean_object* v_key_519_; lean_object* v_val_520_; lean_object* v_rchild_521_; 
lean_dec_ref_known(v___x_490_, 4);
v_lchild_518_ = lean_ctor_get(v_rchild_495_, 0);
lean_inc(v_lchild_518_);
v_key_519_ = lean_ctor_get(v_rchild_495_, 1);
lean_inc(v_key_519_);
v_val_520_ = lean_ctor_get(v_rchild_495_, 2);
lean_inc(v_val_520_);
v_rchild_521_ = lean_ctor_get(v_rchild_495_, 3);
lean_inc(v_rchild_521_);
lean_dec_ref_known(v_rchild_495_, 4);
v_a_497_ = v_lchild_492_;
v_kx_498_ = v_key_493_;
v_vx_499_ = v_val_494_;
v_b_500_ = v_lchild_518_;
v_ky_501_ = v_key_519_;
v_vy_502_ = v_val_520_;
v_c_503_ = v_rchild_521_;
v_kz_504_ = v_key_482_;
v_vz_505_ = v_val_483_;
v_d_506_ = v_rchild_484_;
goto v___jp_496_;
}
else
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref_known(v_lchild_492_, 4);
lean_dec(v_val_494_);
lean_dec(v_key_493_);
lean_del_object(v___x_486_);
v_isSharedCheck_528_ = !lean_is_exclusive(v_rchild_495_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; lean_object* v_unused_530_; lean_object* v_unused_531_; lean_object* v_unused_532_; 
v_unused_529_ = lean_ctor_get(v_rchild_495_, 3);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_rchild_495_, 2);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_rchild_495_, 1);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_rchild_495_, 0);
lean_dec(v_unused_532_);
v___x_523_ = v_rchild_495_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_rchild_495_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 3, v_rchild_484_);
lean_ctor_set(v___x_523_, 2, v_val_483_);
lean_ctor_set(v___x_523_, 1, v_key_482_);
lean_ctor_set(v___x_523_, 0, v___x_490_);
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_key_482_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_val_483_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_rchild_484_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*4, v_color_459_);
return v___x_526_;
}
}
}
}
else
{
lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_rchild_495_);
lean_dec(v_val_494_);
lean_dec(v_key_493_);
lean_del_object(v___x_486_);
v_isSharedCheck_539_ = !lean_is_exclusive(v_lchild_492_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; lean_object* v_unused_541_; lean_object* v_unused_542_; lean_object* v_unused_543_; 
v_unused_540_ = lean_ctor_get(v_lchild_492_, 3);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_lchild_492_, 2);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_lchild_492_, 1);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_lchild_492_, 0);
lean_dec(v_unused_543_);
v___x_534_ = v_lchild_492_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_dec(v_lchild_492_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 3, v_rchild_484_);
lean_ctor_set(v___x_534_, 2, v_val_483_);
lean_ctor_set(v___x_534_, 1, v_key_482_);
lean_ctor_set(v___x_534_, 0, v___x_490_);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_key_482_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_val_483_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_rchild_484_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_ctor_set_uint8(v___x_537_, sizeof(void*)*4, v_color_459_);
return v___x_537_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_495_) == 1)
{
uint8_t v_color_544_; 
v_color_544_ = lean_ctor_get_uint8(v_rchild_495_, sizeof(void*)*4);
if (v_color_544_ == 0)
{
lean_object* v_lchild_545_; lean_object* v_key_546_; lean_object* v_val_547_; lean_object* v_rchild_548_; 
lean_dec_ref_known(v___x_490_, 4);
v_lchild_545_ = lean_ctor_get(v_rchild_495_, 0);
lean_inc(v_lchild_545_);
v_key_546_ = lean_ctor_get(v_rchild_495_, 1);
lean_inc(v_key_546_);
v_val_547_ = lean_ctor_get(v_rchild_495_, 2);
lean_inc(v_val_547_);
v_rchild_548_ = lean_ctor_get(v_rchild_495_, 3);
lean_inc(v_rchild_548_);
lean_dec_ref_known(v_rchild_495_, 4);
v_a_497_ = v_lchild_492_;
v_kx_498_ = v_key_493_;
v_vx_499_ = v_val_494_;
v_b_500_ = v_lchild_545_;
v_ky_501_ = v_key_546_;
v_vy_502_ = v_val_547_;
v_c_503_ = v_rchild_548_;
v_kz_504_ = v_key_482_;
v_vz_505_ = v_val_483_;
v_d_506_ = v_rchild_484_;
goto v___jp_496_;
}
else
{
lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v_val_494_);
lean_dec(v_key_493_);
lean_dec(v_lchild_492_);
lean_del_object(v___x_486_);
v_isSharedCheck_555_ = !lean_is_exclusive(v_rchild_495_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_556_ = lean_ctor_get(v_rchild_495_, 3);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_rchild_495_, 2);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_rchild_495_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_rchild_495_, 0);
lean_dec(v_unused_559_);
v___x_550_ = v_rchild_495_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_dec(v_rchild_495_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 3, v_rchild_484_);
lean_ctor_set(v___x_550_, 2, v_val_483_);
lean_ctor_set(v___x_550_, 1, v_key_482_);
lean_ctor_set(v___x_550_, 0, v___x_490_);
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_key_482_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_val_483_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_rchild_484_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*4, v_color_459_);
return v___x_553_;
}
}
}
}
else
{
lean_object* v___x_560_; 
lean_dec(v_rchild_495_);
lean_dec(v_val_494_);
lean_dec(v_key_493_);
lean_dec(v_lchild_492_);
lean_del_object(v___x_486_);
v___x_560_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_560_, 0, v___x_490_);
lean_ctor_set(v___x_560_, 1, v_key_482_);
lean_ctor_set(v___x_560_, 2, v_val_483_);
lean_ctor_set(v___x_560_, 3, v_rchild_484_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*4, v_color_459_);
return v___x_560_;
}
}
}
else
{
lean_object* v___x_561_; 
lean_dec(v_rchild_495_);
lean_dec(v_val_494_);
lean_dec(v_key_493_);
lean_dec(v_lchild_492_);
lean_del_object(v___x_486_);
v___x_561_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_561_, 0, v___x_490_);
lean_ctor_set(v___x_561_, 1, v_key_482_);
lean_ctor_set(v___x_561_, 2, v_val_483_);
lean_ctor_set(v___x_561_, 3, v_rchild_484_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*4, v_color_459_);
return v___x_561_;
}
v___jp_496_:
{
lean_object* v___x_508_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 3, v_b_500_);
lean_ctor_set(v___x_486_, 2, v_vx_499_);
lean_ctor_set(v___x_486_, 1, v_kx_498_);
lean_ctor_set(v___x_486_, 0, v_a_497_);
v___x_508_ = v___x_486_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_497_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_kx_498_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_vx_499_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_b_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_511_, sizeof(void*)*4, v_color_459_);
v___x_508_ = v_reuseFailAlloc_511_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_509_, 0, v_c_503_);
lean_ctor_set(v___x_509_, 1, v_kz_504_);
lean_ctor_set(v___x_509_, 2, v_vz_505_);
lean_ctor_set(v___x_509_, 3, v_d_506_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*4, v_color_459_);
v___x_510_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v_ky_501_);
lean_ctor_set(v___x_510_, 2, v_vy_502_);
lean_ctor_set(v___x_510_, 3, v___x_509_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*4, v_color_491_);
return v___x_510_;
}
}
}
else
{
lean_object* v___x_563_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_490_);
v___x_563_ = v___x_486_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_key_482_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_val_483_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_rchild_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_564_, sizeof(void*)*4, v_color_459_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
case 1:
{
lean_object* v___x_566_; 
lean_dec(v_val_483_);
lean_dec(v_key_482_);
lean_dec_ref(v_cmp_453_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 2, v_x_456_);
lean_ctor_set(v___x_486_, 1, v_x_455_);
v___x_566_ = v___x_486_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_lchild_481_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_x_455_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_x_456_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v_rchild_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_567_, sizeof(void*)*4, v_color_459_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
default: 
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_453_, v_rchild_484_, v_x_455_, v_x_456_);
if (lean_obj_tag(v___x_568_) == 1)
{
uint8_t v_color_569_; lean_object* v_lchild_570_; lean_object* v_key_571_; lean_object* v_val_572_; lean_object* v_rchild_573_; lean_object* v_a_575_; lean_object* v_kx_576_; lean_object* v_vx_577_; lean_object* v_b_578_; lean_object* v_ky_579_; lean_object* v_vy_580_; lean_object* v_c_581_; lean_object* v_kz_582_; lean_object* v_vz_583_; lean_object* v_d_584_; 
v_color_569_ = lean_ctor_get_uint8(v___x_568_, sizeof(void*)*4);
v_lchild_570_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_lchild_570_);
v_key_571_ = lean_ctor_get(v___x_568_, 1);
lean_inc(v_key_571_);
v_val_572_ = lean_ctor_get(v___x_568_, 2);
lean_inc(v_val_572_);
v_rchild_573_ = lean_ctor_get(v___x_568_, 3);
lean_inc(v_rchild_573_);
if (v_color_569_ == 0)
{
if (lean_obj_tag(v_lchild_570_) == 1)
{
uint8_t v_color_590_; 
v_color_590_ = lean_ctor_get_uint8(v_lchild_570_, sizeof(void*)*4);
if (v_color_590_ == 0)
{
lean_object* v_lchild_591_; lean_object* v_key_592_; lean_object* v_val_593_; lean_object* v_rchild_594_; 
lean_dec_ref_known(v___x_568_, 4);
v_lchild_591_ = lean_ctor_get(v_lchild_570_, 0);
lean_inc(v_lchild_591_);
v_key_592_ = lean_ctor_get(v_lchild_570_, 1);
lean_inc(v_key_592_);
v_val_593_ = lean_ctor_get(v_lchild_570_, 2);
lean_inc(v_val_593_);
v_rchild_594_ = lean_ctor_get(v_lchild_570_, 3);
lean_inc(v_rchild_594_);
lean_dec_ref_known(v_lchild_570_, 4);
v_a_575_ = v_lchild_481_;
v_kx_576_ = v_key_482_;
v_vx_577_ = v_val_483_;
v_b_578_ = v_lchild_591_;
v_ky_579_ = v_key_592_;
v_vy_580_ = v_val_593_;
v_c_581_ = v_rchild_594_;
v_kz_582_ = v_key_571_;
v_vz_583_ = v_val_572_;
v_d_584_ = v_rchild_573_;
goto v___jp_574_;
}
else
{
if (lean_obj_tag(v_rchild_573_) == 1)
{
uint8_t v_color_595_; 
v_color_595_ = lean_ctor_get_uint8(v_rchild_573_, sizeof(void*)*4);
if (v_color_595_ == 0)
{
lean_object* v_lchild_596_; lean_object* v_key_597_; lean_object* v_val_598_; lean_object* v_rchild_599_; 
lean_dec_ref_known(v___x_568_, 4);
v_lchild_596_ = lean_ctor_get(v_rchild_573_, 0);
lean_inc(v_lchild_596_);
v_key_597_ = lean_ctor_get(v_rchild_573_, 1);
lean_inc(v_key_597_);
v_val_598_ = lean_ctor_get(v_rchild_573_, 2);
lean_inc(v_val_598_);
v_rchild_599_ = lean_ctor_get(v_rchild_573_, 3);
lean_inc(v_rchild_599_);
lean_dec_ref_known(v_rchild_573_, 4);
v_a_575_ = v_lchild_481_;
v_kx_576_ = v_key_482_;
v_vx_577_ = v_val_483_;
v_b_578_ = v_lchild_570_;
v_ky_579_ = v_key_571_;
v_vy_580_ = v_val_572_;
v_c_581_ = v_lchild_596_;
v_kz_582_ = v_key_597_;
v_vz_583_ = v_val_598_;
v_d_584_ = v_rchild_599_;
goto v___jp_574_;
}
else
{
lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec_ref_known(v_lchild_570_, 4);
lean_dec(v_val_572_);
lean_dec(v_key_571_);
lean_del_object(v___x_486_);
v_isSharedCheck_606_ = !lean_is_exclusive(v_rchild_573_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; lean_object* v_unused_608_; lean_object* v_unused_609_; lean_object* v_unused_610_; 
v_unused_607_ = lean_ctor_get(v_rchild_573_, 3);
lean_dec(v_unused_607_);
v_unused_608_ = lean_ctor_get(v_rchild_573_, 2);
lean_dec(v_unused_608_);
v_unused_609_ = lean_ctor_get(v_rchild_573_, 1);
lean_dec(v_unused_609_);
v_unused_610_ = lean_ctor_get(v_rchild_573_, 0);
lean_dec(v_unused_610_);
v___x_601_ = v_rchild_573_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_dec(v_rchild_573_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 3, v___x_568_);
lean_ctor_set(v___x_601_, 2, v_val_483_);
lean_ctor_set(v___x_601_, 1, v_key_482_);
lean_ctor_set(v___x_601_, 0, v_lchild_481_);
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_lchild_481_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_key_482_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_val_483_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v___x_568_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_ctor_set_uint8(v___x_604_, sizeof(void*)*4, v_color_459_);
return v___x_604_;
}
}
}
}
else
{
lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_rchild_573_);
lean_dec(v_val_572_);
lean_dec(v_key_571_);
lean_del_object(v___x_486_);
v_isSharedCheck_617_ = !lean_is_exclusive(v_lchild_570_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; 
v_unused_618_ = lean_ctor_get(v_lchild_570_, 3);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_lchild_570_, 2);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_lchild_570_, 1);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_lchild_570_, 0);
lean_dec(v_unused_621_);
v___x_612_ = v_lchild_570_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_dec(v_lchild_570_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 3, v___x_568_);
lean_ctor_set(v___x_612_, 2, v_val_483_);
lean_ctor_set(v___x_612_, 1, v_key_482_);
lean_ctor_set(v___x_612_, 0, v_lchild_481_);
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_lchild_481_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_key_482_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_val_483_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v___x_568_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*4, v_color_459_);
return v___x_615_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_573_) == 1)
{
uint8_t v_color_622_; 
v_color_622_ = lean_ctor_get_uint8(v_rchild_573_, sizeof(void*)*4);
if (v_color_622_ == 0)
{
lean_object* v_lchild_623_; lean_object* v_key_624_; lean_object* v_val_625_; lean_object* v_rchild_626_; 
lean_dec_ref_known(v___x_568_, 4);
v_lchild_623_ = lean_ctor_get(v_rchild_573_, 0);
lean_inc(v_lchild_623_);
v_key_624_ = lean_ctor_get(v_rchild_573_, 1);
lean_inc(v_key_624_);
v_val_625_ = lean_ctor_get(v_rchild_573_, 2);
lean_inc(v_val_625_);
v_rchild_626_ = lean_ctor_get(v_rchild_573_, 3);
lean_inc(v_rchild_626_);
lean_dec_ref_known(v_rchild_573_, 4);
v_a_575_ = v_lchild_481_;
v_kx_576_ = v_key_482_;
v_vx_577_ = v_val_483_;
v_b_578_ = v_lchild_570_;
v_ky_579_ = v_key_571_;
v_vy_580_ = v_val_572_;
v_c_581_ = v_lchild_623_;
v_kz_582_ = v_key_624_;
v_vz_583_ = v_val_625_;
v_d_584_ = v_rchild_626_;
goto v___jp_574_;
}
else
{
lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_val_572_);
lean_dec(v_key_571_);
lean_dec(v_lchild_570_);
lean_del_object(v___x_486_);
v_isSharedCheck_633_ = !lean_is_exclusive(v_rchild_573_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; lean_object* v_unused_635_; lean_object* v_unused_636_; lean_object* v_unused_637_; 
v_unused_634_ = lean_ctor_get(v_rchild_573_, 3);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_rchild_573_, 2);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_rchild_573_, 1);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_rchild_573_, 0);
lean_dec(v_unused_637_);
v___x_628_ = v_rchild_573_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_dec(v_rchild_573_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 3, v___x_568_);
lean_ctor_set(v___x_628_, 2, v_val_483_);
lean_ctor_set(v___x_628_, 1, v_key_482_);
lean_ctor_set(v___x_628_, 0, v_lchild_481_);
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_lchild_481_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_key_482_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_val_483_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v___x_568_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*4, v_color_459_);
return v___x_631_;
}
}
}
}
else
{
lean_object* v___x_638_; 
lean_dec(v_rchild_573_);
lean_dec(v_val_572_);
lean_dec(v_key_571_);
lean_dec(v_lchild_570_);
lean_del_object(v___x_486_);
v___x_638_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_638_, 0, v_lchild_481_);
lean_ctor_set(v___x_638_, 1, v_key_482_);
lean_ctor_set(v___x_638_, 2, v_val_483_);
lean_ctor_set(v___x_638_, 3, v___x_568_);
lean_ctor_set_uint8(v___x_638_, sizeof(void*)*4, v_color_459_);
return v___x_638_;
}
}
}
else
{
lean_object* v___x_639_; 
lean_dec(v_rchild_573_);
lean_dec(v_val_572_);
lean_dec(v_key_571_);
lean_dec(v_lchild_570_);
lean_del_object(v___x_486_);
v___x_639_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_639_, 0, v_lchild_481_);
lean_ctor_set(v___x_639_, 1, v_key_482_);
lean_ctor_set(v___x_639_, 2, v_val_483_);
lean_ctor_set(v___x_639_, 3, v___x_568_);
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*4, v_color_459_);
return v___x_639_;
}
v___jp_574_:
{
lean_object* v___x_586_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 3, v_b_578_);
lean_ctor_set(v___x_486_, 2, v_vx_577_);
lean_ctor_set(v___x_486_, 1, v_kx_576_);
lean_ctor_set(v___x_486_, 0, v_a_575_);
v___x_586_ = v___x_486_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_575_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_kx_576_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_vx_577_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_b_578_);
lean_ctor_set_uint8(v_reuseFailAlloc_589_, sizeof(void*)*4, v_color_459_);
v___x_586_ = v_reuseFailAlloc_589_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_587_, 0, v_c_581_);
lean_ctor_set(v___x_587_, 1, v_kz_582_);
lean_ctor_set(v___x_587_, 2, v_vz_583_);
lean_ctor_set(v___x_587_, 3, v_d_584_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*4, v_color_459_);
v___x_588_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v_ky_579_);
lean_ctor_set(v___x_588_, 2, v_vy_580_);
lean_ctor_set(v___x_588_, 3, v___x_587_);
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*4, v_color_569_);
return v___x_588_;
}
}
}
else
{
lean_object* v___x_641_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 3, v___x_568_);
v___x_641_ = v___x_486_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_lchild_481_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_key_482_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_val_483_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v___x_568_);
lean_ctor_set_uint8(v_reuseFailAlloc_642_, sizeof(void*)*4, v_color_459_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(lean_object* v_cmp_644_, lean_object* v_t_645_, lean_object* v_k_646_, lean_object* v_v_647_){
_start:
{
uint8_t v___x_648_; 
v___x_648_ = l_Lean_RBNode_isRed___redArg(v_t_645_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_644_, v_t_645_, v_k_646_, v_v_647_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_644_, v_t_645_, v_k_646_, v_v_647_);
v___x_651_ = l_Lean_RBNode_setBlack___redArg(v___x_650_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(lean_object* v_cmp_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_dec_ref(v_cmp_652_);
return v_x_653_;
}
else
{
lean_object* v_head_655_; lean_object* v_tail_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_head_655_ = lean_ctor_get(v_x_654_, 0);
lean_inc(v_head_655_);
v_tail_656_ = lean_ctor_get(v_x_654_, 1);
lean_inc(v_tail_656_);
lean_dec_ref_known(v_x_654_, 2);
v___x_657_ = lean_box(0);
lean_inc_ref(v_cmp_652_);
v___x_658_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_652_, v_x_653_, v_head_655_, v___x_657_);
v_x_653_ = v___x_658_;
v_x_654_ = v_tail_656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList___redArg(lean_object* v_l_660_, lean_object* v_cmp_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_box(0);
v___x_663_ = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(v_cmp_661_, v___x_662_, v_l_660_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList(lean_object* v_00_u03b1_664_, lean_object* v_l_665_, lean_object* v_cmp_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_RBTree_fromList___redArg(v_l_665_, v_cmp_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0(lean_object* v_00_u03b1_668_, lean_object* v_cmp_669_, lean_object* v_00_u03b2_670_, lean_object* v_t_671_, lean_object* v_k_672_, lean_object* v_v_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_669_, v_t_671_, v_k_672_, v_v_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1(lean_object* v_00_u03b1_675_, lean_object* v_cmp_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(v_cmp_676_, v_x_677_, v_x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0(lean_object* v_00_u03b1_680_, lean_object* v_cmp_681_, lean_object* v_00_u03b2_682_, lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_681_, v_x_683_, v_x_684_, v_x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(lean_object* v_cmp_687_, lean_object* v_as_688_, size_t v_i_689_, size_t v_stop_690_, lean_object* v_b_691_){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = lean_usize_dec_eq(v_i_689_, v_stop_690_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; size_t v___x_696_; size_t v___x_697_; 
v___x_693_ = lean_array_uget_borrowed(v_as_688_, v_i_689_);
v___x_694_ = lean_box(0);
lean_inc(v___x_693_);
lean_inc_ref(v_cmp_687_);
v___x_695_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_687_, v_b_691_, v___x_693_, v___x_694_);
v___x_696_ = ((size_t)1ULL);
v___x_697_ = lean_usize_add(v_i_689_, v___x_696_);
v_i_689_ = v___x_697_;
v_b_691_ = v___x_695_;
goto _start;
}
else
{
lean_dec_ref(v_cmp_687_);
return v_b_691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg___boxed(lean_object* v_cmp_699_, lean_object* v_as_700_, lean_object* v_i_701_, lean_object* v_stop_702_, lean_object* v_b_703_){
_start:
{
size_t v_i_boxed_704_; size_t v_stop_boxed_705_; lean_object* v_res_706_; 
v_i_boxed_704_ = lean_unbox_usize(v_i_701_);
lean_dec(v_i_701_);
v_stop_boxed_705_ = lean_unbox_usize(v_stop_702_);
lean_dec(v_stop_702_);
v_res_706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_699_, v_as_700_, v_i_boxed_704_, v_stop_boxed_705_, v_b_703_);
lean_dec_ref(v_as_700_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg(lean_object* v_l_707_, lean_object* v_cmp_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_709_ = lean_box(0);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_array_get_size(v_l_707_);
v___x_712_ = lean_nat_dec_lt(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec_ref(v_cmp_708_);
return v___x_709_;
}
else
{
uint8_t v___x_713_; 
v___x_713_ = lean_nat_dec_le(v___x_711_, v___x_711_);
if (v___x_713_ == 0)
{
if (v___x_712_ == 0)
{
lean_dec_ref(v_cmp_708_);
return v___x_709_;
}
else
{
size_t v___x_714_; size_t v___x_715_; lean_object* v___x_716_; 
v___x_714_ = ((size_t)0ULL);
v___x_715_ = lean_usize_of_nat(v___x_711_);
v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_708_, v_l_707_, v___x_714_, v___x_715_, v___x_709_);
return v___x_716_;
}
}
else
{
size_t v___x_717_; size_t v___x_718_; lean_object* v___x_719_; 
v___x_717_ = ((size_t)0ULL);
v___x_718_ = lean_usize_of_nat(v___x_711_);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_708_, v_l_707_, v___x_717_, v___x_718_, v___x_709_);
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg___boxed(lean_object* v_l_720_, lean_object* v_cmp_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_RBTree_fromArray___redArg(v_l_720_, v_cmp_721_);
lean_dec_ref(v_l_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray(lean_object* v_00_u03b1_723_, lean_object* v_l_724_, lean_object* v_cmp_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_RBTree_fromArray___redArg(v_l_724_, v_cmp_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___boxed(lean_object* v_00_u03b1_727_, lean_object* v_l_728_, lean_object* v_cmp_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_RBTree_fromArray(v_00_u03b1_727_, v_l_728_, v_cmp_729_);
lean_dec_ref(v_l_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(lean_object* v_00_u03b1_731_, lean_object* v_cmp_732_, lean_object* v_as_733_, size_t v_i_734_, size_t v_stop_735_, lean_object* v_b_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_732_, v_as_733_, v_i_734_, v_stop_735_, v_b_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___boxed(lean_object* v_00_u03b1_738_, lean_object* v_cmp_739_, lean_object* v_as_740_, lean_object* v_i_741_, lean_object* v_stop_742_, lean_object* v_b_743_){
_start:
{
size_t v_i_boxed_744_; size_t v_stop_boxed_745_; lean_object* v_res_746_; 
v_i_boxed_744_ = lean_unbox_usize(v_i_741_);
lean_dec(v_i_741_);
v_stop_boxed_745_ = lean_unbox_usize(v_stop_742_);
lean_dec(v_stop_742_);
v_res_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(v_00_u03b1_738_, v_cmp_739_, v_as_740_, v_i_boxed_744_, v_stop_boxed_745_, v_b_743_);
lean_dec_ref(v_as_740_);
return v_res_746_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_all___redArg___lam__0(lean_object* v_p_747_, lean_object* v_a_748_, lean_object* v_x_749_){
_start:
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_apply_1(v_p_747_, v_a_748_);
v___x_751_ = lean_unbox(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___lam__0___boxed(lean_object* v_p_752_, lean_object* v_a_753_, lean_object* v_x_754_){
_start:
{
uint8_t v_res_755_; lean_object* v_r_756_; 
v_res_755_ = l_Lean_RBTree_all___redArg___lam__0(v_p_752_, v_a_753_, v_x_754_);
v_r_756_ = lean_box(v_res_755_);
return v_r_756_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_all___redArg(lean_object* v_t_757_, lean_object* v_p_758_){
_start:
{
lean_object* v___f_759_; uint8_t v___x_760_; 
v___f_759_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_759_, 0, v_p_758_);
v___x_760_ = l_Lean_RBNode_all___redArg(v___f_759_, v_t_757_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___boxed(lean_object* v_t_761_, lean_object* v_p_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l_Lean_RBTree_all___redArg(v_t_761_, v_p_762_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_all(lean_object* v_00_u03b1_765_, lean_object* v_cmp_766_, lean_object* v_t_767_, lean_object* v_p_768_){
_start:
{
lean_object* v___f_769_; uint8_t v___x_770_; 
v___f_769_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_769_, 0, v_p_768_);
v___x_770_ = l_Lean_RBNode_all___redArg(v___f_769_, v_t_767_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___boxed(lean_object* v_00_u03b1_771_, lean_object* v_cmp_772_, lean_object* v_t_773_, lean_object* v_p_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l_Lean_RBTree_all(v_00_u03b1_771_, v_cmp_772_, v_t_773_, v_p_774_);
lean_dec_ref(v_cmp_772_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_any___redArg(lean_object* v_t_777_, lean_object* v_p_778_){
_start:
{
lean_object* v___f_779_; uint8_t v___x_780_; 
v___f_779_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_779_, 0, v_p_778_);
v___x_780_ = l_Lean_RBNode_any___redArg(v___f_779_, v_t_777_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_any___redArg___boxed(lean_object* v_t_781_, lean_object* v_p_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_Lean_RBTree_any___redArg(v_t_781_, v_p_782_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_any(lean_object* v_00_u03b1_785_, lean_object* v_cmp_786_, lean_object* v_t_787_, lean_object* v_p_788_){
_start:
{
lean_object* v___f_789_; uint8_t v___x_790_; 
v___f_789_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_789_, 0, v_p_788_);
v___x_790_ = l_Lean_RBNode_any___redArg(v___f_789_, v_t_787_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_any___boxed(lean_object* v_00_u03b1_791_, lean_object* v_cmp_792_, lean_object* v_t_793_, lean_object* v_p_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_Lean_RBTree_any(v_00_u03b1_791_, v_cmp_792_, v_t_793_, v_p_794_);
lean_dec_ref(v_cmp_792_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(lean_object* v_cmp_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_798_) == 0)
{
lean_object* v___x_800_; 
lean_dec(v_x_799_);
lean_dec_ref(v_cmp_797_);
v___x_800_ = lean_box(0);
return v___x_800_;
}
else
{
lean_object* v_lchild_801_; lean_object* v_key_802_; lean_object* v_val_803_; lean_object* v_rchild_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_lchild_801_ = lean_ctor_get(v_x_798_, 0);
lean_inc(v_lchild_801_);
v_key_802_ = lean_ctor_get(v_x_798_, 1);
lean_inc_n(v_key_802_, 2);
v_val_803_ = lean_ctor_get(v_x_798_, 2);
lean_inc(v_val_803_);
v_rchild_804_ = lean_ctor_get(v_x_798_, 3);
lean_inc(v_rchild_804_);
lean_dec_ref_known(v_x_798_, 4);
lean_inc_ref(v_cmp_797_);
lean_inc(v_x_799_);
v___x_805_ = lean_apply_2(v_cmp_797_, v_x_799_, v_key_802_);
v___x_806_ = lean_unbox(v___x_805_);
switch(v___x_806_)
{
case 0:
{
lean_dec(v_rchild_804_);
lean_dec(v_val_803_);
lean_dec(v_key_802_);
v_x_798_ = v_lchild_801_;
goto _start;
}
case 1:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_rchild_804_);
lean_dec(v_lchild_801_);
lean_dec(v_x_799_);
lean_dec_ref(v_cmp_797_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v_key_802_);
lean_ctor_set(v___x_808_, 1, v_val_803_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
default: 
{
lean_dec(v_val_803_);
lean_dec(v_key_802_);
lean_dec(v_lchild_801_);
v_x_798_ = v_rchild_804_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(lean_object* v_t_u2082_811_, lean_object* v_cmp_812_, lean_object* v_x_813_){
_start:
{
if (lean_obj_tag(v_x_813_) == 0)
{
uint8_t v___x_814_; 
lean_dec_ref(v_cmp_812_);
lean_dec(v_t_u2082_811_);
v___x_814_ = 1;
return v___x_814_;
}
else
{
lean_object* v_lchild_815_; lean_object* v_key_816_; lean_object* v_rchild_817_; lean_object* v___x_818_; 
v_lchild_815_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_lchild_815_);
v_key_816_ = lean_ctor_get(v_x_813_, 1);
lean_inc(v_key_816_);
v_rchild_817_ = lean_ctor_get(v_x_813_, 3);
lean_inc(v_rchild_817_);
lean_dec_ref_known(v_x_813_, 4);
lean_inc(v_t_u2082_811_);
lean_inc_ref(v_cmp_812_);
v___x_818_ = l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(v_cmp_812_, v_t_u2082_811_, v_key_816_);
if (lean_obj_tag(v___x_818_) == 0)
{
uint8_t v___x_819_; 
lean_dec(v_rchild_817_);
lean_dec(v_lchild_815_);
lean_dec_ref(v_cmp_812_);
lean_dec(v_t_u2082_811_);
v___x_819_ = 0;
return v___x_819_;
}
else
{
uint8_t v___x_820_; 
lean_dec_ref_known(v___x_818_, 1);
lean_inc_ref(v_cmp_812_);
lean_inc(v_t_u2082_811_);
v___x_820_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_811_, v_cmp_812_, v_lchild_815_);
if (v___x_820_ == 0)
{
lean_dec(v_rchild_817_);
lean_dec_ref(v_cmp_812_);
lean_dec(v_t_u2082_811_);
return v___x_820_;
}
else
{
v_x_813_ = v_rchild_817_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg___boxed(lean_object* v_t_u2082_822_, lean_object* v_cmp_823_, lean_object* v_x_824_){
_start:
{
uint8_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_822_, v_cmp_823_, v_x_824_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_subset___redArg(lean_object* v_cmp_827_, lean_object* v_t_u2081_828_, lean_object* v_t_u2082_829_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_829_, v_cmp_827_, v_t_u2081_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___redArg___boxed(lean_object* v_cmp_831_, lean_object* v_t_u2081_832_, lean_object* v_t_u2082_833_){
_start:
{
uint8_t v_res_834_; lean_object* v_r_835_; 
v_res_834_ = l_Lean_RBTree_subset___redArg(v_cmp_831_, v_t_u2081_832_, v_t_u2082_833_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_subset(lean_object* v_00_u03b1_836_, lean_object* v_cmp_837_, lean_object* v_t_u2081_838_, lean_object* v_t_u2082_839_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_839_, v_cmp_837_, v_t_u2081_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___boxed(lean_object* v_00_u03b1_841_, lean_object* v_cmp_842_, lean_object* v_t_u2081_843_, lean_object* v_t_u2082_844_){
_start:
{
uint8_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l_Lean_RBTree_subset(v_00_u03b1_841_, v_cmp_842_, v_t_u2081_843_, v_t_u2082_844_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0(lean_object* v_00_u03b1_847_, lean_object* v_cmp_848_, lean_object* v_00_u03b2_849_, lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(v_cmp_848_, v_x_850_, v_x_851_);
return v___x_852_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(lean_object* v_00_u03b1_853_, lean_object* v_t_u2082_854_, lean_object* v_cmp_855_, lean_object* v_x_856_){
_start:
{
uint8_t v___x_857_; 
v___x_857_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_854_, v_cmp_855_, v_x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___boxed(lean_object* v_00_u03b1_858_, lean_object* v_t_u2082_859_, lean_object* v_cmp_860_, lean_object* v_x_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(v_00_u03b1_858_, v_t_u2082_859_, v_cmp_860_, v_x_861_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_seteq___redArg(lean_object* v_cmp_864_, lean_object* v_t_u2081_865_, lean_object* v_t_u2082_866_){
_start:
{
uint8_t v___x_867_; 
lean_inc(v_t_u2081_865_);
lean_inc_ref(v_cmp_864_);
lean_inc(v_t_u2082_866_);
v___x_867_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_866_, v_cmp_864_, v_t_u2081_865_);
if (v___x_867_ == 0)
{
lean_dec(v_t_u2082_866_);
lean_dec(v_t_u2081_865_);
lean_dec_ref(v_cmp_864_);
return v___x_867_;
}
else
{
uint8_t v___x_868_; 
v___x_868_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2081_865_, v_cmp_864_, v_t_u2082_866_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___redArg___boxed(lean_object* v_cmp_869_, lean_object* v_t_u2081_870_, lean_object* v_t_u2082_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l_Lean_RBTree_seteq___redArg(v_cmp_869_, v_t_u2081_870_, v_t_u2082_871_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_seteq(lean_object* v_00_u03b1_874_, lean_object* v_cmp_875_, lean_object* v_t_u2081_876_, lean_object* v_t_u2082_877_){
_start:
{
uint8_t v___x_878_; 
v___x_878_ = l_Lean_RBTree_seteq___redArg(v_cmp_875_, v_t_u2081_876_, v_t_u2082_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___boxed(lean_object* v_00_u03b1_879_, lean_object* v_cmp_880_, lean_object* v_t_u2081_881_, lean_object* v_t_u2082_882_){
_start:
{
uint8_t v_res_883_; lean_object* v_r_884_; 
v_res_883_ = l_Lean_RBTree_seteq(v_00_u03b1_879_, v_cmp_880_, v_t_u2081_881_, v_t_u2082_882_);
v_r_884_ = lean_box(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(lean_object* v_cmp_885_, lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
if (lean_obj_tag(v_x_887_) == 0)
{
lean_dec_ref(v_cmp_885_);
return v_x_886_;
}
else
{
lean_object* v_lchild_888_; lean_object* v_key_889_; lean_object* v_rchild_890_; lean_object* v_val_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_lchild_888_ = lean_ctor_get(v_x_887_, 0);
lean_inc(v_lchild_888_);
v_key_889_ = lean_ctor_get(v_x_887_, 1);
lean_inc(v_key_889_);
v_rchild_890_ = lean_ctor_get(v_x_887_, 3);
lean_inc(v_rchild_890_);
lean_dec_ref_known(v_x_887_, 4);
lean_inc_ref_n(v_cmp_885_, 2);
v_val_891_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(v_cmp_885_, v_x_886_, v_lchild_888_);
v___x_892_ = lean_box(0);
v___x_893_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_885_, v_val_891_, v_key_889_, v___x_892_);
v_x_886_ = v___x_893_;
v_x_887_ = v_rchild_890_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_union___redArg(lean_object* v_cmp_895_, lean_object* v_t_u2081_896_, lean_object* v_t_u2082_897_){
_start:
{
if (lean_obj_tag(v_t_u2081_896_) == 0)
{
lean_dec_ref(v_cmp_895_);
return v_t_u2082_897_;
}
else
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(v_cmp_895_, v_t_u2081_896_, v_t_u2082_897_);
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_union(lean_object* v_00_u03b1_899_, lean_object* v_cmp_900_, lean_object* v_t_u2081_901_, lean_object* v_t_u2082_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_RBTree_union___redArg(v_cmp_900_, v_t_u2081_901_, v_t_u2082_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0(lean_object* v_00_u03b1_904_, lean_object* v_cmp_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(v_cmp_905_, v_x_906_, v_x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(lean_object* v_cmp_909_, lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
if (lean_obj_tag(v_x_911_) == 0)
{
lean_dec(v_x_910_);
lean_dec_ref(v_cmp_909_);
return v_x_911_;
}
else
{
lean_object* v_lchild_912_; lean_object* v_key_913_; lean_object* v_val_914_; lean_object* v_rchild_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_938_; 
v_lchild_912_ = lean_ctor_get(v_x_911_, 0);
v_key_913_ = lean_ctor_get(v_x_911_, 1);
v_val_914_ = lean_ctor_get(v_x_911_, 2);
v_rchild_915_ = lean_ctor_get(v_x_911_, 3);
v_isSharedCheck_938_ = !lean_is_exclusive(v_x_911_);
if (v_isSharedCheck_938_ == 0)
{
v___x_917_ = v_x_911_;
v_isShared_918_ = v_isSharedCheck_938_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_rchild_915_);
lean_inc(v_val_914_);
lean_inc(v_key_913_);
lean_inc(v_lchild_912_);
lean_dec(v_x_911_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_938_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; uint8_t v___x_920_; 
lean_inc_ref(v_cmp_909_);
lean_inc(v_key_913_);
lean_inc(v_x_910_);
v___x_919_ = lean_apply_2(v_cmp_909_, v_x_910_, v_key_913_);
v___x_920_ = lean_unbox(v___x_919_);
switch(v___x_920_)
{
case 0:
{
uint8_t v___x_921_; 
v___x_921_ = l_Lean_RBNode_isBlack___redArg(v_lchild_912_);
if (v___x_921_ == 0)
{
uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_922_ = 0;
v___x_923_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_909_, v_x_910_, v_lchild_912_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_923_);
v___x_925_ = v___x_917_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_key_913_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_val_914_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_rchild_915_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_ctor_set_uint8(v___x_925_, sizeof(void*)*4, v___x_922_);
return v___x_925_;
}
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_del_object(v___x_917_);
v___x_927_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_909_, v_x_910_, v_lchild_912_);
v___x_928_ = l_Lean_RBNode_balLeft___redArg(v___x_927_, v_key_913_, v_val_914_, v_rchild_915_);
return v___x_928_;
}
}
case 1:
{
lean_object* v___x_929_; 
lean_del_object(v___x_917_);
lean_dec(v_val_914_);
lean_dec(v_key_913_);
lean_dec(v_x_910_);
lean_dec_ref(v_cmp_909_);
v___x_929_ = l_Lean_RBNode_appendTrees___redArg(v_lchild_912_, v_rchild_915_);
return v___x_929_;
}
default: 
{
uint8_t v___x_930_; 
v___x_930_ = l_Lean_RBNode_isBlack___redArg(v_rchild_915_);
if (v___x_930_ == 0)
{
uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_931_ = 0;
v___x_932_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_909_, v_x_910_, v_rchild_915_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 3, v___x_932_);
v___x_934_ = v___x_917_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_lchild_912_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_key_913_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_val_914_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*4, v___x_931_);
return v___x_934_;
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_del_object(v___x_917_);
v___x_936_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_909_, v_x_910_, v_rchild_915_);
v___x_937_ = l_Lean_RBNode_balRight___redArg(v_lchild_912_, v_key_913_, v_val_914_, v___x_936_);
return v___x_937_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(lean_object* v_cmp_939_, lean_object* v_x_940_, lean_object* v_t_941_){
_start:
{
lean_object* v_t_942_; lean_object* v___x_943_; 
v_t_942_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_939_, v_x_940_, v_t_941_);
v___x_943_ = l_Lean_RBNode_setBlack___redArg(v_t_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(lean_object* v_cmp_944_, lean_object* v_x_945_, lean_object* v_x_946_){
_start:
{
if (lean_obj_tag(v_x_946_) == 0)
{
lean_dec_ref(v_cmp_944_);
return v_x_945_;
}
else
{
lean_object* v_lchild_947_; lean_object* v_key_948_; lean_object* v_rchild_949_; lean_object* v_val_950_; lean_object* v___x_951_; 
v_lchild_947_ = lean_ctor_get(v_x_946_, 0);
lean_inc(v_lchild_947_);
v_key_948_ = lean_ctor_get(v_x_946_, 1);
lean_inc(v_key_948_);
v_rchild_949_ = lean_ctor_get(v_x_946_, 3);
lean_inc(v_rchild_949_);
lean_dec_ref_known(v_x_946_, 4);
lean_inc_ref_n(v_cmp_944_, 2);
v_val_950_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_944_, v_x_945_, v_lchild_947_);
v___x_951_ = l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(v_cmp_944_, v_key_948_, v_val_950_);
v_x_945_ = v___x_951_;
v_x_946_ = v_rchild_949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_diff___redArg(lean_object* v_cmp_953_, lean_object* v_t_u2081_954_, lean_object* v_t_u2082_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_953_, v_t_u2081_954_, v_t_u2082_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_diff(lean_object* v_00_u03b1_957_, lean_object* v_cmp_958_, lean_object* v_t_u2081_959_, lean_object* v_t_u2082_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_958_, v_t_u2081_959_, v_t_u2082_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0(lean_object* v_00_u03b1_962_, lean_object* v_cmp_963_, lean_object* v_00_u03b2_964_, lean_object* v_x_965_, lean_object* v_t_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(v_cmp_963_, v_x_965_, v_t_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1(lean_object* v_00_u03b1_968_, lean_object* v_cmp_969_, lean_object* v_x_970_, lean_object* v_x_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_969_, v_x_970_, v_x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0(lean_object* v_00_u03b1_973_, lean_object* v_cmp_974_, lean_object* v_00_u03b2_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_974_, v_x_976_, v_x_977_);
return v___x_978_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_filter___redArg___lam__0(lean_object* v_f_979_, lean_object* v_a_980_, lean_object* v_x_981_){
_start:
{
lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_982_ = lean_apply_1(v_f_979_, v_a_980_);
v___x_983_ = lean_unbox(v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg___lam__0___boxed(lean_object* v_f_984_, lean_object* v_a_985_, lean_object* v_x_986_){
_start:
{
uint8_t v_res_987_; lean_object* v_r_988_; 
v_res_987_ = l_Lean_RBTree_filter___redArg___lam__0(v_f_984_, v_a_985_, v_x_986_);
v_r_988_ = lean_box(v_res_987_);
return v_r_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg(lean_object* v_cmp_989_, lean_object* v_f_990_, lean_object* v_m_991_){
_start:
{
lean_object* v___f_992_; lean_object* v___x_993_; 
v___f_992_ = lean_alloc_closure((void*)(l_Lean_RBTree_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_992_, 0, v_f_990_);
v___x_993_ = l_Lean_RBMap_filter___redArg(v_cmp_989_, v___f_992_, v_m_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter(lean_object* v_00_u03b1_994_, lean_object* v_cmp_995_, lean_object* v_f_996_, lean_object* v_m_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_RBTree_filter___redArg(v_cmp_995_, v_f_996_, v_m_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbtreeOf___redArg(lean_object* v_l_999_, lean_object* v_cmp_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_RBTree_fromList___redArg(v_l_999_, v_cmp_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbtreeOf(lean_object* v_00_u03b1_1002_, lean_object* v_l_1003_, lean_object* v_cmp_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_RBTree_fromList___redArg(v_l_1003_, v_cmp_1004_);
return v___x_1005_;
}
}
lean_object* runtime_initialize_Lean_Data_RBMap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_RBTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_RBMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_RBTree(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_RBTree(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_RBMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_RBTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_RBTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_RBTree(builtin);
}
#ifdef __cplusplus
}
#endif
