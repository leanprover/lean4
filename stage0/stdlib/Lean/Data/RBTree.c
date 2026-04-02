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
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRBTree___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree(lean_object* v_00_u03b1_1_, lean_object* v_p_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___boxed(lean_object* v_00_u03b1_4_, lean_object* v_p_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_instInhabitedRBTree(v_00_u03b1_4_, v_p_5_);
lean_dec_ref(v_p_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBTree(lean_object* v_00_u03b1_7_, lean_object* v_cmp_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBTree___boxed(lean_object* v_00_u03b1_10_, lean_object* v_cmp_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_mkRBTree(v_00_u03b1_10_, v_cmp_11_);
lean_dec_ref(v_cmp_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree(lean_object* v_00_u03b1_13_, lean_object* v_cmp_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___boxed(lean_object* v_00_u03b1_16_, lean_object* v_cmp_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_instEmptyCollectionRBTree(v_00_u03b1_16_, v_cmp_17_);
lean_dec_ref(v_cmp_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_empty(lean_object* v_00_u03b1_19_, lean_object* v_cmp_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_box(0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_empty___boxed(lean_object* v_00_u03b1_22_, lean_object* v_cmp_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_RBTree_empty(v_00_u03b1_22_, v_cmp_23_);
lean_dec_ref(v_cmp_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg(lean_object* v_f_25_, lean_object* v_t_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_RBNode_depth___redArg(v_f_25_, v_t_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg___boxed(lean_object* v_f_28_, lean_object* v_t_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_RBTree_depth___redArg(v_f_28_, v_t_29_);
lean_dec(v_t_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth(lean_object* v_00_u03b1_31_, lean_object* v_cmp_32_, lean_object* v_f_33_, lean_object* v_t_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_RBNode_depth___redArg(v_f_33_, v_t_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___boxed(lean_object* v_00_u03b1_36_, lean_object* v_cmp_37_, lean_object* v_f_38_, lean_object* v_t_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_RBTree_depth(v_00_u03b1_36_, v_cmp_37_, v_f_38_, v_t_39_);
lean_dec(v_t_39_);
lean_dec_ref(v_cmp_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg___lam__0(lean_object* v_f_41_, lean_object* v_r_42_, lean_object* v_a_43_, lean_object* v_x_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_apply_2(v_f_41_, v_r_42_, v_a_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg(lean_object* v_f_46_, lean_object* v_init_47_, lean_object* v_t_48_){
_start:
{
lean_object* v___f_49_; lean_object* v___x_50_; 
v___f_49_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_49_, 0, v_f_46_);
v___x_50_ = l_Lean_RBNode_fold___redArg(v___f_49_, v_init_47_, v_t_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold(lean_object* v_00_u03b1_51_, lean_object* v_00_u03b2_52_, lean_object* v_cmp_53_, lean_object* v_f_54_, lean_object* v_init_55_, lean_object* v_t_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___x_58_; 
v___f_57_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_57_, 0, v_f_54_);
v___x_58_ = l_Lean_RBNode_fold___redArg(v___f_57_, v_init_55_, v_t_56_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___boxed(lean_object* v_00_u03b1_59_, lean_object* v_00_u03b2_60_, lean_object* v_cmp_61_, lean_object* v_f_62_, lean_object* v_init_63_, lean_object* v_t_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_RBTree_fold(v_00_u03b1_59_, v_00_u03b2_60_, v_cmp_61_, v_f_62_, v_init_63_, v_t_64_);
lean_dec_ref(v_cmp_61_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___redArg(lean_object* v_f_66_, lean_object* v_init_67_, lean_object* v_t_68_){
_start:
{
lean_object* v___f_69_; lean_object* v___x_70_; 
v___f_69_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_69_, 0, v_f_66_);
v___x_70_ = l_Lean_RBNode_revFold___redArg(v___f_69_, v_init_67_, v_t_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold(lean_object* v_00_u03b1_71_, lean_object* v_00_u03b2_72_, lean_object* v_cmp_73_, lean_object* v_f_74_, lean_object* v_init_75_, lean_object* v_t_76_){
_start:
{
lean_object* v___f_77_; lean_object* v___x_78_; 
v___f_77_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_77_, 0, v_f_74_);
v___x_78_ = l_Lean_RBNode_revFold___redArg(v___f_77_, v_init_75_, v_t_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___boxed(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_cmp_81_, lean_object* v_f_82_, lean_object* v_init_83_, lean_object* v_t_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_RBTree_revFold(v_00_u03b1_79_, v_00_u03b2_80_, v_cmp_81_, v_f_82_, v_init_83_, v_t_84_);
lean_dec_ref(v_cmp_81_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___redArg(lean_object* v_inst_86_, lean_object* v_f_87_, lean_object* v_init_88_, lean_object* v_t_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___x_91_; 
v___f_90_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_90_, 0, v_f_87_);
v___x_91_ = l_Lean_RBNode_foldM___redArg(v_inst_86_, v___f_90_, v_init_88_, v_t_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM(lean_object* v_00_u03b1_92_, lean_object* v_00_u03b2_93_, lean_object* v_cmp_94_, lean_object* v_m_95_, lean_object* v_inst_96_, lean_object* v_f_97_, lean_object* v_init_98_, lean_object* v_t_99_){
_start:
{
lean_object* v___f_100_; lean_object* v___x_101_; 
v___f_100_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_100_, 0, v_f_97_);
v___x_101_ = l_Lean_RBNode_foldM___redArg(v_inst_96_, v___f_100_, v_init_98_, v_t_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___boxed(lean_object* v_00_u03b1_102_, lean_object* v_00_u03b2_103_, lean_object* v_cmp_104_, lean_object* v_m_105_, lean_object* v_inst_106_, lean_object* v_f_107_, lean_object* v_init_108_, lean_object* v_t_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_RBTree_foldM(v_00_u03b1_102_, v_00_u03b2_103_, v_cmp_104_, v_m_105_, v_inst_106_, v_f_107_, v_init_108_, v_t_109_);
lean_dec_ref(v_cmp_104_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg___lam__0(lean_object* v_f_111_, lean_object* v_r_112_, lean_object* v_a_113_, lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_apply_1(v_f_111_, v_a_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg(lean_object* v_inst_116_, lean_object* v_f_117_, lean_object* v_t_118_){
_start:
{
lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___f_119_ = lean_alloc_closure((void*)(l_Lean_RBTree_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_119_, 0, v_f_117_);
v___x_120_ = lean_box(0);
v___x_121_ = l_Lean_RBNode_foldM___redArg(v_inst_116_, v___f_119_, v___x_120_, v_t_118_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM(lean_object* v_00_u03b1_122_, lean_object* v_cmp_123_, lean_object* v_m_124_, lean_object* v_inst_125_, lean_object* v_f_126_, lean_object* v_t_127_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___f_128_ = lean_alloc_closure((void*)(l_Lean_RBTree_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_128_, 0, v_f_126_);
v___x_129_ = lean_box(0);
v___x_130_ = l_Lean_RBNode_foldM___redArg(v_inst_125_, v___f_128_, v___x_129_, v_t_127_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___boxed(lean_object* v_00_u03b1_131_, lean_object* v_cmp_132_, lean_object* v_m_133_, lean_object* v_inst_134_, lean_object* v_f_135_, lean_object* v_t_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_RBTree_forM(v_00_u03b1_131_, v_cmp_132_, v_m_133_, v_inst_134_, v_f_135_, v_t_136_);
lean_dec_ref(v_cmp_132_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__0(lean_object* v_f_138_, lean_object* v_a_139_, lean_object* v_x_140_, lean_object* v_acc_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_apply_2(v_f_138_, v_a_139_, v_acc_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__1(lean_object* v_toPure_143_, lean_object* v_____do__lift_144_){
_start:
{
lean_object* v_a_145_; lean_object* v___x_146_; 
v_a_145_ = lean_ctor_get(v_____do__lift_144_, 0);
lean_inc(v_a_145_);
lean_dec_ref(v_____do__lift_144_);
v___x_146_ = lean_apply_2(v_toPure_143_, lean_box(0), v_a_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg(lean_object* v_inst_147_, lean_object* v_t_148_, lean_object* v_init_149_, lean_object* v_f_150_){
_start:
{
lean_object* v_toApplicative_151_; lean_object* v_toBind_152_; lean_object* v_toPure_153_; lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v___f_156_; lean_object* v___x_157_; 
v_toApplicative_151_ = lean_ctor_get(v_inst_147_, 0);
v_toBind_152_ = lean_ctor_get(v_inst_147_, 1);
lean_inc(v_toBind_152_);
v_toPure_153_ = lean_ctor_get(v_toApplicative_151_, 1);
lean_inc(v_toPure_153_);
v___f_154_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_154_, 0, v_f_150_);
v___x_155_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_147_, v___f_154_, v_t_148_, v_init_149_);
v___f_156_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_156_, 0, v_toPure_153_);
v___x_157_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v___x_155_, v___f_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn(lean_object* v_00_u03b1_158_, lean_object* v_cmp_159_, lean_object* v_m_160_, lean_object* v_00_u03c3_161_, lean_object* v_inst_162_, lean_object* v_t_163_, lean_object* v_init_164_, lean_object* v_f_165_){
_start:
{
lean_object* v_toApplicative_166_; lean_object* v_toBind_167_; lean_object* v_toPure_168_; lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___f_171_; lean_object* v___x_172_; 
v_toApplicative_166_ = lean_ctor_get(v_inst_162_, 0);
v_toBind_167_ = lean_ctor_get(v_inst_162_, 1);
lean_inc(v_toBind_167_);
v_toPure_168_ = lean_ctor_get(v_toApplicative_166_, 1);
lean_inc(v_toPure_168_);
v___f_169_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_169_, 0, v_f_165_);
v___x_170_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_162_, v___f_169_, v_t_163_, v_init_164_);
v___f_171_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_171_, 0, v_toPure_168_);
v___x_172_ = lean_apply_4(v_toBind_167_, lean_box(0), lean_box(0), v___x_170_, v___f_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___boxed(lean_object* v_00_u03b1_173_, lean_object* v_cmp_174_, lean_object* v_m_175_, lean_object* v_00_u03c3_176_, lean_object* v_inst_177_, lean_object* v_t_178_, lean_object* v_init_179_, lean_object* v_f_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_RBTree_forIn(v_00_u03b1_173_, v_cmp_174_, v_m_175_, v_00_u03c3_176_, v_inst_177_, v_t_178_, v_init_179_, v_f_180_);
lean_dec_ref(v_cmp_174_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__0(lean_object* v___y_182_, lean_object* v_a_183_, lean_object* v_x_184_, lean_object* v_acc_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_apply_2(v___y_182_, v_a_183_, v_acc_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__2(lean_object* v_inst_187_, lean_object* v_00_u03b2_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_toApplicative_192_; lean_object* v_toBind_193_; lean_object* v_toPure_194_; lean_object* v___f_195_; lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v_toApplicative_192_ = lean_ctor_get(v_inst_187_, 0);
v_toBind_193_ = lean_ctor_get(v_inst_187_, 1);
lean_inc(v_toBind_193_);
v_toPure_194_ = lean_ctor_get(v_toApplicative_192_, 1);
lean_inc(v_toPure_194_);
v___f_195_ = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_195_, 0, v___y_191_);
v___x_196_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_187_, v___f_195_, v___y_189_, v___y_190_);
v___f_197_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_197_, 0, v_toPure_194_);
v___x_198_ = lean_apply_4(v_toBind_193_, lean_box(0), lean_box(0), v___x_196_, v___f_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg(lean_object* v_inst_199_){
_start:
{
lean_object* v___f_200_; 
v___f_200_ = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_200_, 0, v_inst_199_);
return v___f_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad(lean_object* v_00_u03b1_201_, lean_object* v_cmp_202_, lean_object* v_m_203_, lean_object* v_inst_204_){
_start:
{
lean_object* v___f_205_; 
v___f_205_ = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_205_, 0, v_inst_204_);
return v___f_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___boxed(lean_object* v_00_u03b1_206_, lean_object* v_cmp_207_, lean_object* v_m_208_, lean_object* v_inst_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_RBTree_instForInOfMonad(v_00_u03b1_206_, v_cmp_207_, v_m_208_, v_inst_209_);
lean_dec_ref(v_cmp_207_);
return v_res_210_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_isEmpty___redArg(lean_object* v_t_211_){
_start:
{
if (lean_obj_tag(v_t_211_) == 0)
{
uint8_t v___x_212_; 
v___x_212_ = 1;
return v___x_212_;
}
else
{
uint8_t v___x_213_; 
v___x_213_ = 0;
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___redArg___boxed(lean_object* v_t_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_Lean_RBTree_isEmpty___redArg(v_t_214_);
lean_dec(v_t_214_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_isEmpty(lean_object* v_00_u03b1_217_, lean_object* v_cmp_218_, lean_object* v_t_219_){
_start:
{
if (lean_obj_tag(v_t_219_) == 0)
{
uint8_t v___x_220_; 
v___x_220_ = 1;
return v___x_220_;
}
else
{
uint8_t v___x_221_; 
v___x_221_ = 0;
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___boxed(lean_object* v_00_u03b1_222_, lean_object* v_cmp_223_, lean_object* v_t_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Lean_RBTree_isEmpty(v_00_u03b1_222_, v_cmp_223_, v_t_224_);
lean_dec(v_t_224_);
lean_dec_ref(v_cmp_223_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg___lam__0(lean_object* v_r_227_, lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v_a_228_);
lean_ctor_set(v___x_230_, 1, v_r_227_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg(lean_object* v_t_232_){
_start:
{
lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___f_233_ = ((lean_object*)(l_Lean_RBTree_toList___redArg___closed__0));
v___x_234_ = lean_box(0);
v___x_235_ = l_Lean_RBNode_revFold___redArg(v___f_233_, v___x_234_, v_t_232_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList(lean_object* v_00_u03b1_236_, lean_object* v_cmp_237_, lean_object* v_t_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_RBTree_toList___redArg(v_t_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___boxed(lean_object* v_00_u03b1_240_, lean_object* v_cmp_241_, lean_object* v_t_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_RBTree_toList(v_00_u03b1_240_, v_cmp_241_, v_t_242_);
lean_dec_ref(v_cmp_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg___lam__0(lean_object* v_r_244_, lean_object* v_a_245_, lean_object* v_x_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_array_push(v_r_244_, v_a_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg(lean_object* v_t_251_){
_start:
{
lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___f_252_ = ((lean_object*)(l_Lean_RBTree_toArray___redArg___closed__0));
v___x_253_ = ((lean_object*)(l_Lean_RBTree_toArray___redArg___closed__1));
v___x_254_ = l_Lean_RBNode_fold___redArg(v___f_252_, v___x_253_, v_t_251_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray(lean_object* v_00_u03b1_255_, lean_object* v_cmp_256_, lean_object* v_t_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_RBTree_toArray___redArg(v_t_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___boxed(lean_object* v_00_u03b1_259_, lean_object* v_cmp_260_, lean_object* v_t_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_RBTree_toArray(v_00_u03b1_259_, v_cmp_260_, v_t_261_);
lean_dec_ref(v_cmp_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg(lean_object* v_t_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_RBNode_min___redArg(v_t_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_box(0);
return v___x_265_;
}
else
{
lean_object* v_val_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_val_266_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v___x_264_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_val_266_);
lean_dec(v___x_264_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_fst_270_; lean_object* v___x_272_; 
v_fst_270_ = lean_ctor_get(v_val_266_, 0);
lean_inc(v_fst_270_);
lean_dec(v_val_266_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v_fst_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_fst_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg___boxed(lean_object* v_t_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_RBTree_min___redArg(v_t_275_);
lean_dec(v_t_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min(lean_object* v_00_u03b1_277_, lean_object* v_cmp_278_, lean_object* v_t_279_){
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
LEAN_EXPORT lean_object* l_Lean_RBTree_min___boxed(lean_object* v_00_u03b1_291_, lean_object* v_cmp_292_, lean_object* v_t_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_RBTree_min(v_00_u03b1_291_, v_cmp_292_, v_t_293_);
lean_dec(v_t_293_);
lean_dec_ref(v_cmp_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg(lean_object* v_t_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_RBNode_max___redArg(v_t_295_);
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
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg___boxed(lean_object* v_t_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_RBTree_max___redArg(v_t_307_);
lean_dec(v_t_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max(lean_object* v_00_u03b1_309_, lean_object* v_cmp_310_, lean_object* v_t_311_){
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
LEAN_EXPORT lean_object* l_Lean_RBTree_max___boxed(lean_object* v_00_u03b1_323_, lean_object* v_cmp_324_, lean_object* v_t_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_RBTree_max(v_00_u03b1_323_, v_cmp_324_, v_t_325_);
lean_dec(v_t_325_);
lean_dec_ref(v_cmp_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0(lean_object* v_inst_330_, lean_object* v_t_331_, lean_object* v_prec_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_333_ = ((lean_object*)(l_Lean_RBTree_instRepr___redArg___lam__0___closed__1));
v___x_334_ = l_Lean_RBTree_toList___redArg(v_t_331_);
v___x_335_ = l_List_repr___redArg(v_inst_330_, v___x_334_);
v___x_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_333_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = l_Repr_addAppParen(v___x_336_, v_prec_332_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0___boxed(lean_object* v_inst_338_, lean_object* v_t_339_, lean_object* v_prec_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_RBTree_instRepr___redArg___lam__0(v_inst_338_, v_t_339_, v_prec_340_);
lean_dec(v_prec_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg(lean_object* v_inst_342_){
_start:
{
lean_object* v___f_343_; 
v___f_343_ = lean_alloc_closure((void*)(l_Lean_RBTree_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_343_, 0, v_inst_342_);
return v___f_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr(lean_object* v_00_u03b1_344_, lean_object* v_cmp_345_, lean_object* v_inst_346_){
_start:
{
lean_object* v___f_347_; 
v___f_347_ = lean_alloc_closure((void*)(l_Lean_RBTree_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_347_, 0, v_inst_346_);
return v___f_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___boxed(lean_object* v_00_u03b1_348_, lean_object* v_cmp_349_, lean_object* v_inst_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_RBTree_instRepr(v_00_u03b1_348_, v_cmp_349_, v_inst_350_);
lean_dec_ref(v_cmp_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_insert___redArg(lean_object* v_cmp_352_, lean_object* v_t_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_box(0);
v___x_356_ = l_Lean_RBNode_insert___redArg(v_cmp_352_, v_t_353_, v_a_354_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_insert(lean_object* v_00_u03b1_357_, lean_object* v_cmp_358_, lean_object* v_t_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_box(0);
v___x_362_ = l_Lean_RBNode_insert___redArg(v_cmp_358_, v_t_359_, v_a_360_, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_erase___redArg(lean_object* v_cmp_363_, lean_object* v_t_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_RBNode_erase___redArg(v_cmp_363_, v_a_365_, v_t_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_erase(lean_object* v_00_u03b1_367_, lean_object* v_cmp_368_, lean_object* v_t_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_RBNode_erase___redArg(v_cmp_368_, v_a_370_, v_t_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___redArg(lean_object* v_cmp_372_, lean_object* v_x_373_){
_start:
{
if (lean_obj_tag(v_x_373_) == 0)
{
lean_object* v___x_374_; 
lean_dec_ref(v_cmp_372_);
v___x_374_ = lean_box(0);
return v___x_374_;
}
else
{
lean_object* v_head_375_; lean_object* v_tail_376_; lean_object* v_val_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_head_375_ = lean_ctor_get(v_x_373_, 0);
lean_inc(v_head_375_);
v_tail_376_ = lean_ctor_get(v_x_373_, 1);
lean_inc(v_tail_376_);
lean_dec_ref(v_x_373_);
lean_inc_ref(v_cmp_372_);
v_val_377_ = l_Lean_RBTree_ofList___redArg(v_cmp_372_, v_tail_376_);
v___x_378_ = lean_box(0);
v___x_379_ = l_Lean_RBNode_insert___redArg(v_cmp_372_, v_val_377_, v_head_375_, v___x_378_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList(lean_object* v_00_u03b1_380_, lean_object* v_cmp_381_, lean_object* v_x_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_RBTree_ofList___redArg(v_cmp_381_, v_x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f___redArg(lean_object* v_cmp_384_, lean_object* v_t_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_RBNode_findCore___redArg(v_cmp_384_, v_t_385_, v_a_386_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v___x_388_; 
v___x_388_ = lean_box(0);
return v___x_388_;
}
else
{
lean_object* v_val_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_397_; 
v_val_389_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_397_ == 0)
{
v___x_391_ = v___x_387_;
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_val_389_);
lean_dec(v___x_387_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_fst_393_; lean_object* v___x_395_; 
v_fst_393_ = lean_ctor_get(v_val_389_, 0);
lean_inc(v_fst_393_);
lean_dec(v_val_389_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v_fst_393_);
v___x_395_ = v___x_391_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_fst_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f(lean_object* v_00_u03b1_398_, lean_object* v_cmp_399_, lean_object* v_t_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_RBNode_findCore___redArg(v_cmp_399_, v_t_400_, v_a_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_box(0);
return v___x_403_;
}
else
{
lean_object* v_val_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_val_404_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_402_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_val_404_);
lean_dec(v___x_402_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_fst_408_; lean_object* v___x_410_; 
v_fst_408_ = lean_ctor_get(v_val_404_, 0);
lean_inc(v_fst_408_);
lean_dec(v_val_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v_fst_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_fst_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_contains___redArg(lean_object* v_cmp_413_, lean_object* v_t_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_RBNode_findCore___redArg(v_cmp_413_, v_t_414_, v_a_415_);
if (lean_obj_tag(v___x_416_) == 0)
{
uint8_t v___x_417_; 
v___x_417_ = 0;
return v___x_417_;
}
else
{
uint8_t v___x_418_; 
lean_dec_ref(v___x_416_);
v___x_418_ = 1;
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___redArg___boxed(lean_object* v_cmp_419_, lean_object* v_t_420_, lean_object* v_a_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Lean_RBTree_contains___redArg(v_cmp_419_, v_t_420_, v_a_421_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_contains(lean_object* v_00_u03b1_424_, lean_object* v_cmp_425_, lean_object* v_t_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_RBNode_findCore___redArg(v_cmp_425_, v_t_426_, v_a_427_);
if (lean_obj_tag(v___x_428_) == 0)
{
uint8_t v___x_429_; 
v___x_429_ = 0;
return v___x_429_;
}
else
{
uint8_t v___x_430_; 
lean_dec_ref(v___x_428_);
v___x_430_ = 1;
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___boxed(lean_object* v_00_u03b1_431_, lean_object* v_cmp_432_, lean_object* v_t_433_, lean_object* v_a_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Lean_RBTree_contains(v_00_u03b1_431_, v_cmp_432_, v_t_433_, v_a_434_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(lean_object* v_cmp_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_438_) == 0)
{
uint8_t v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v_cmp_437_);
v___x_441_ = 0;
v___x_442_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_442_, 0, v_x_438_);
lean_ctor_set(v___x_442_, 1, v_x_439_);
lean_ctor_set(v___x_442_, 2, v_x_440_);
lean_ctor_set(v___x_442_, 3, v_x_438_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*4, v___x_441_);
return v___x_442_;
}
else
{
uint8_t v_color_443_; 
v_color_443_ = lean_ctor_get_uint8(v_x_438_, sizeof(void*)*4);
if (v_color_443_ == 0)
{
lean_object* v_lchild_444_; lean_object* v_key_445_; lean_object* v_val_446_; lean_object* v_rchild_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_464_; 
v_lchild_444_ = lean_ctor_get(v_x_438_, 0);
v_key_445_ = lean_ctor_get(v_x_438_, 1);
v_val_446_ = lean_ctor_get(v_x_438_, 2);
v_rchild_447_ = lean_ctor_get(v_x_438_, 3);
v_isSharedCheck_464_ = !lean_is_exclusive(v_x_438_);
if (v_isSharedCheck_464_ == 0)
{
v___x_449_ = v_x_438_;
v_isShared_450_ = v_isSharedCheck_464_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_rchild_447_);
lean_inc(v_val_446_);
lean_inc(v_key_445_);
lean_inc(v_lchild_444_);
lean_dec(v_x_438_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_464_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; uint8_t v___x_452_; 
lean_inc_ref(v_cmp_437_);
lean_inc(v_key_445_);
lean_inc(v_x_439_);
v___x_451_ = lean_apply_2(v_cmp_437_, v_x_439_, v_key_445_);
v___x_452_ = lean_unbox(v___x_451_);
switch(v___x_452_)
{
case 0:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_437_, v_lchild_444_, v_x_439_, v_x_440_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_453_);
v___x_455_ = v___x_449_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_key_445_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_val_446_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_rchild_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_456_, sizeof(void*)*4, v_color_443_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
case 1:
{
lean_object* v___x_458_; 
lean_dec(v_val_446_);
lean_dec(v_key_445_);
lean_dec_ref(v_cmp_437_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 2, v_x_440_);
lean_ctor_set(v___x_449_, 1, v_x_439_);
v___x_458_ = v___x_449_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_lchild_444_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_x_439_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_x_440_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_rchild_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_459_, sizeof(void*)*4, v_color_443_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
default: 
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_437_, v_rchild_447_, v_x_439_, v_x_440_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 3, v___x_460_);
v___x_462_ = v___x_449_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_lchild_444_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_key_445_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_val_446_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v___x_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*4, v_color_443_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
else
{
lean_object* v_lchild_465_; lean_object* v_key_466_; lean_object* v_val_467_; lean_object* v_rchild_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_627_; 
v_lchild_465_ = lean_ctor_get(v_x_438_, 0);
v_key_466_ = lean_ctor_get(v_x_438_, 1);
v_val_467_ = lean_ctor_get(v_x_438_, 2);
v_rchild_468_ = lean_ctor_get(v_x_438_, 3);
v_isSharedCheck_627_ = !lean_is_exclusive(v_x_438_);
if (v_isSharedCheck_627_ == 0)
{
v___x_470_ = v_x_438_;
v_isShared_471_ = v_isSharedCheck_627_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_rchild_468_);
lean_inc(v_val_467_);
lean_inc(v_key_466_);
lean_inc(v_lchild_465_);
lean_dec(v_x_438_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_627_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; uint8_t v___x_473_; 
lean_inc_ref(v_cmp_437_);
lean_inc(v_key_466_);
lean_inc(v_x_439_);
v___x_472_ = lean_apply_2(v_cmp_437_, v_x_439_, v_key_466_);
v___x_473_ = lean_unbox(v___x_472_);
switch(v___x_473_)
{
case 0:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_437_, v_lchild_465_, v_x_439_, v_x_440_);
if (lean_obj_tag(v___x_474_) == 1)
{
uint8_t v_color_475_; lean_object* v_lchild_476_; lean_object* v_key_477_; lean_object* v_val_478_; lean_object* v_rchild_479_; lean_object* v_a_481_; lean_object* v_kx_482_; lean_object* v_vx_483_; lean_object* v_b_484_; lean_object* v_ky_485_; lean_object* v_vy_486_; lean_object* v_c_487_; lean_object* v_kz_488_; lean_object* v_vz_489_; lean_object* v_d_490_; 
v_color_475_ = lean_ctor_get_uint8(v___x_474_, sizeof(void*)*4);
v_lchild_476_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_lchild_476_);
v_key_477_ = lean_ctor_get(v___x_474_, 1);
lean_inc(v_key_477_);
v_val_478_ = lean_ctor_get(v___x_474_, 2);
lean_inc(v_val_478_);
v_rchild_479_ = lean_ctor_get(v___x_474_, 3);
lean_inc(v_rchild_479_);
if (v_color_475_ == 0)
{
if (lean_obj_tag(v_lchild_476_) == 1)
{
uint8_t v_color_496_; 
v_color_496_ = lean_ctor_get_uint8(v_lchild_476_, sizeof(void*)*4);
if (v_color_496_ == 0)
{
lean_object* v_lchild_497_; lean_object* v_key_498_; lean_object* v_val_499_; lean_object* v_rchild_500_; 
lean_dec_ref(v___x_474_);
v_lchild_497_ = lean_ctor_get(v_lchild_476_, 0);
lean_inc(v_lchild_497_);
v_key_498_ = lean_ctor_get(v_lchild_476_, 1);
lean_inc(v_key_498_);
v_val_499_ = lean_ctor_get(v_lchild_476_, 2);
lean_inc(v_val_499_);
v_rchild_500_ = lean_ctor_get(v_lchild_476_, 3);
lean_inc(v_rchild_500_);
lean_dec_ref(v_lchild_476_);
v_a_481_ = v_lchild_497_;
v_kx_482_ = v_key_498_;
v_vx_483_ = v_val_499_;
v_b_484_ = v_rchild_500_;
v_ky_485_ = v_key_477_;
v_vy_486_ = v_val_478_;
v_c_487_ = v_rchild_479_;
v_kz_488_ = v_key_466_;
v_vz_489_ = v_val_467_;
v_d_490_ = v_rchild_468_;
goto v___jp_480_;
}
else
{
if (lean_obj_tag(v_rchild_479_) == 1)
{
uint8_t v_color_501_; 
v_color_501_ = lean_ctor_get_uint8(v_rchild_479_, sizeof(void*)*4);
if (v_color_501_ == 0)
{
lean_object* v_lchild_502_; lean_object* v_key_503_; lean_object* v_val_504_; lean_object* v_rchild_505_; 
lean_dec_ref(v___x_474_);
v_lchild_502_ = lean_ctor_get(v_rchild_479_, 0);
lean_inc(v_lchild_502_);
v_key_503_ = lean_ctor_get(v_rchild_479_, 1);
lean_inc(v_key_503_);
v_val_504_ = lean_ctor_get(v_rchild_479_, 2);
lean_inc(v_val_504_);
v_rchild_505_ = lean_ctor_get(v_rchild_479_, 3);
lean_inc(v_rchild_505_);
lean_dec_ref(v_rchild_479_);
v_a_481_ = v_lchild_476_;
v_kx_482_ = v_key_477_;
v_vx_483_ = v_val_478_;
v_b_484_ = v_lchild_502_;
v_ky_485_ = v_key_503_;
v_vy_486_ = v_val_504_;
v_c_487_ = v_rchild_505_;
v_kz_488_ = v_key_466_;
v_vz_489_ = v_val_467_;
v_d_490_ = v_rchild_468_;
goto v___jp_480_;
}
else
{
lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec_ref(v_lchild_476_);
lean_dec(v_val_478_);
lean_dec(v_key_477_);
lean_del_object(v___x_470_);
v_isSharedCheck_512_ = !lean_is_exclusive(v_rchild_479_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; lean_object* v_unused_514_; lean_object* v_unused_515_; lean_object* v_unused_516_; 
v_unused_513_ = lean_ctor_get(v_rchild_479_, 3);
lean_dec(v_unused_513_);
v_unused_514_ = lean_ctor_get(v_rchild_479_, 2);
lean_dec(v_unused_514_);
v_unused_515_ = lean_ctor_get(v_rchild_479_, 1);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_rchild_479_, 0);
lean_dec(v_unused_516_);
v___x_507_ = v_rchild_479_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_dec(v_rchild_479_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 3, v_rchild_468_);
lean_ctor_set(v___x_507_, 2, v_val_467_);
lean_ctor_set(v___x_507_, 1, v_key_466_);
lean_ctor_set(v___x_507_, 0, v___x_474_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_key_466_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_val_467_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_rchild_468_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*4, v_color_443_);
return v___x_510_;
}
}
}
}
else
{
lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v_rchild_479_);
lean_dec(v_val_478_);
lean_dec(v_key_477_);
lean_del_object(v___x_470_);
v_isSharedCheck_523_ = !lean_is_exclusive(v_lchild_476_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; lean_object* v_unused_525_; lean_object* v_unused_526_; lean_object* v_unused_527_; 
v_unused_524_ = lean_ctor_get(v_lchild_476_, 3);
lean_dec(v_unused_524_);
v_unused_525_ = lean_ctor_get(v_lchild_476_, 2);
lean_dec(v_unused_525_);
v_unused_526_ = lean_ctor_get(v_lchild_476_, 1);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_lchild_476_, 0);
lean_dec(v_unused_527_);
v___x_518_ = v_lchild_476_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_dec(v_lchild_476_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 3, v_rchild_468_);
lean_ctor_set(v___x_518_, 2, v_val_467_);
lean_ctor_set(v___x_518_, 1, v_key_466_);
lean_ctor_set(v___x_518_, 0, v___x_474_);
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_key_466_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_val_467_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_rchild_468_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*4, v_color_443_);
return v___x_521_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_479_) == 1)
{
uint8_t v_color_528_; 
v_color_528_ = lean_ctor_get_uint8(v_rchild_479_, sizeof(void*)*4);
if (v_color_528_ == 0)
{
lean_object* v_lchild_529_; lean_object* v_key_530_; lean_object* v_val_531_; lean_object* v_rchild_532_; 
lean_dec_ref(v___x_474_);
v_lchild_529_ = lean_ctor_get(v_rchild_479_, 0);
lean_inc(v_lchild_529_);
v_key_530_ = lean_ctor_get(v_rchild_479_, 1);
lean_inc(v_key_530_);
v_val_531_ = lean_ctor_get(v_rchild_479_, 2);
lean_inc(v_val_531_);
v_rchild_532_ = lean_ctor_get(v_rchild_479_, 3);
lean_inc(v_rchild_532_);
lean_dec_ref(v_rchild_479_);
v_a_481_ = v_lchild_476_;
v_kx_482_ = v_key_477_;
v_vx_483_ = v_val_478_;
v_b_484_ = v_lchild_529_;
v_ky_485_ = v_key_530_;
v_vy_486_ = v_val_531_;
v_c_487_ = v_rchild_532_;
v_kz_488_ = v_key_466_;
v_vz_489_ = v_val_467_;
v_d_490_ = v_rchild_468_;
goto v___jp_480_;
}
else
{
lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_val_478_);
lean_dec(v_key_477_);
lean_dec(v_lchild_476_);
lean_del_object(v___x_470_);
v_isSharedCheck_539_ = !lean_is_exclusive(v_rchild_479_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; lean_object* v_unused_541_; lean_object* v_unused_542_; lean_object* v_unused_543_; 
v_unused_540_ = lean_ctor_get(v_rchild_479_, 3);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_rchild_479_, 2);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_rchild_479_, 1);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_rchild_479_, 0);
lean_dec(v_unused_543_);
v___x_534_ = v_rchild_479_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_dec(v_rchild_479_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 3, v_rchild_468_);
lean_ctor_set(v___x_534_, 2, v_val_467_);
lean_ctor_set(v___x_534_, 1, v_key_466_);
lean_ctor_set(v___x_534_, 0, v___x_474_);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_key_466_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_val_467_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_rchild_468_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_ctor_set_uint8(v___x_537_, sizeof(void*)*4, v_color_443_);
return v___x_537_;
}
}
}
}
else
{
lean_object* v___x_544_; 
lean_dec(v_rchild_479_);
lean_dec(v_val_478_);
lean_dec(v_key_477_);
lean_dec(v_lchild_476_);
lean_del_object(v___x_470_);
v___x_544_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_544_, 0, v___x_474_);
lean_ctor_set(v___x_544_, 1, v_key_466_);
lean_ctor_set(v___x_544_, 2, v_val_467_);
lean_ctor_set(v___x_544_, 3, v_rchild_468_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*4, v_color_443_);
return v___x_544_;
}
}
}
else
{
lean_object* v___x_545_; 
lean_dec(v_rchild_479_);
lean_dec(v_val_478_);
lean_dec(v_key_477_);
lean_dec(v_lchild_476_);
lean_del_object(v___x_470_);
v___x_545_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_545_, 0, v___x_474_);
lean_ctor_set(v___x_545_, 1, v_key_466_);
lean_ctor_set(v___x_545_, 2, v_val_467_);
lean_ctor_set(v___x_545_, 3, v_rchild_468_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*4, v_color_443_);
return v___x_545_;
}
v___jp_480_:
{
lean_object* v___x_492_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 3, v_b_484_);
lean_ctor_set(v___x_470_, 2, v_vx_483_);
lean_ctor_set(v___x_470_, 1, v_kx_482_);
lean_ctor_set(v___x_470_, 0, v_a_481_);
v___x_492_ = v___x_470_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_481_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_kx_482_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_vx_483_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_b_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*4, v_color_443_);
v___x_492_ = v_reuseFailAlloc_495_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_493_, 0, v_c_487_);
lean_ctor_set(v___x_493_, 1, v_kz_488_);
lean_ctor_set(v___x_493_, 2, v_vz_489_);
lean_ctor_set(v___x_493_, 3, v_d_490_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*4, v_color_443_);
v___x_494_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v_ky_485_);
lean_ctor_set(v___x_494_, 2, v_vy_486_);
lean_ctor_set(v___x_494_, 3, v___x_493_);
lean_ctor_set_uint8(v___x_494_, sizeof(void*)*4, v_color_475_);
return v___x_494_;
}
}
}
else
{
lean_object* v___x_547_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_474_);
v___x_547_ = v___x_470_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_key_466_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_val_467_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_rchild_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_548_, sizeof(void*)*4, v_color_443_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
case 1:
{
lean_object* v___x_550_; 
lean_dec(v_val_467_);
lean_dec(v_key_466_);
lean_dec_ref(v_cmp_437_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 2, v_x_440_);
lean_ctor_set(v___x_470_, 1, v_x_439_);
v___x_550_ = v___x_470_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_lchild_465_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_x_439_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_x_440_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_rchild_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_551_, sizeof(void*)*4, v_color_443_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
default: 
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_437_, v_rchild_468_, v_x_439_, v_x_440_);
if (lean_obj_tag(v___x_552_) == 1)
{
uint8_t v_color_553_; lean_object* v_lchild_554_; lean_object* v_key_555_; lean_object* v_val_556_; lean_object* v_rchild_557_; lean_object* v_a_559_; lean_object* v_kx_560_; lean_object* v_vx_561_; lean_object* v_b_562_; lean_object* v_ky_563_; lean_object* v_vy_564_; lean_object* v_c_565_; lean_object* v_kz_566_; lean_object* v_vz_567_; lean_object* v_d_568_; 
v_color_553_ = lean_ctor_get_uint8(v___x_552_, sizeof(void*)*4);
v_lchild_554_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_lchild_554_);
v_key_555_ = lean_ctor_get(v___x_552_, 1);
lean_inc(v_key_555_);
v_val_556_ = lean_ctor_get(v___x_552_, 2);
lean_inc(v_val_556_);
v_rchild_557_ = lean_ctor_get(v___x_552_, 3);
lean_inc(v_rchild_557_);
if (v_color_553_ == 0)
{
if (lean_obj_tag(v_lchild_554_) == 1)
{
uint8_t v_color_574_; 
v_color_574_ = lean_ctor_get_uint8(v_lchild_554_, sizeof(void*)*4);
if (v_color_574_ == 0)
{
lean_object* v_lchild_575_; lean_object* v_key_576_; lean_object* v_val_577_; lean_object* v_rchild_578_; 
lean_dec_ref(v___x_552_);
v_lchild_575_ = lean_ctor_get(v_lchild_554_, 0);
lean_inc(v_lchild_575_);
v_key_576_ = lean_ctor_get(v_lchild_554_, 1);
lean_inc(v_key_576_);
v_val_577_ = lean_ctor_get(v_lchild_554_, 2);
lean_inc(v_val_577_);
v_rchild_578_ = lean_ctor_get(v_lchild_554_, 3);
lean_inc(v_rchild_578_);
lean_dec_ref(v_lchild_554_);
v_a_559_ = v_lchild_465_;
v_kx_560_ = v_key_466_;
v_vx_561_ = v_val_467_;
v_b_562_ = v_lchild_575_;
v_ky_563_ = v_key_576_;
v_vy_564_ = v_val_577_;
v_c_565_ = v_rchild_578_;
v_kz_566_ = v_key_555_;
v_vz_567_ = v_val_556_;
v_d_568_ = v_rchild_557_;
goto v___jp_558_;
}
else
{
if (lean_obj_tag(v_rchild_557_) == 1)
{
uint8_t v_color_579_; 
v_color_579_ = lean_ctor_get_uint8(v_rchild_557_, sizeof(void*)*4);
if (v_color_579_ == 0)
{
lean_object* v_lchild_580_; lean_object* v_key_581_; lean_object* v_val_582_; lean_object* v_rchild_583_; 
lean_dec_ref(v___x_552_);
v_lchild_580_ = lean_ctor_get(v_rchild_557_, 0);
lean_inc(v_lchild_580_);
v_key_581_ = lean_ctor_get(v_rchild_557_, 1);
lean_inc(v_key_581_);
v_val_582_ = lean_ctor_get(v_rchild_557_, 2);
lean_inc(v_val_582_);
v_rchild_583_ = lean_ctor_get(v_rchild_557_, 3);
lean_inc(v_rchild_583_);
lean_dec_ref(v_rchild_557_);
v_a_559_ = v_lchild_465_;
v_kx_560_ = v_key_466_;
v_vx_561_ = v_val_467_;
v_b_562_ = v_lchild_554_;
v_ky_563_ = v_key_555_;
v_vy_564_ = v_val_556_;
v_c_565_ = v_lchild_580_;
v_kz_566_ = v_key_581_;
v_vz_567_ = v_val_582_;
v_d_568_ = v_rchild_583_;
goto v___jp_558_;
}
else
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v_lchild_554_);
lean_dec(v_val_556_);
lean_dec(v_key_555_);
lean_del_object(v___x_470_);
v_isSharedCheck_590_ = !lean_is_exclusive(v_rchild_557_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; lean_object* v_unused_592_; lean_object* v_unused_593_; lean_object* v_unused_594_; 
v_unused_591_ = lean_ctor_get(v_rchild_557_, 3);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_rchild_557_, 2);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_rchild_557_, 1);
lean_dec(v_unused_593_);
v_unused_594_ = lean_ctor_get(v_rchild_557_, 0);
lean_dec(v_unused_594_);
v___x_585_ = v_rchild_557_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_dec(v_rchild_557_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 3, v___x_552_);
lean_ctor_set(v___x_585_, 2, v_val_467_);
lean_ctor_set(v___x_585_, 1, v_key_466_);
lean_ctor_set(v___x_585_, 0, v_lchild_465_);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_lchild_465_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_key_466_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_val_467_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v___x_552_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*4, v_color_443_);
return v___x_588_;
}
}
}
}
else
{
lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec(v_rchild_557_);
lean_dec(v_val_556_);
lean_dec(v_key_555_);
lean_del_object(v___x_470_);
v_isSharedCheck_601_ = !lean_is_exclusive(v_lchild_554_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; lean_object* v_unused_603_; lean_object* v_unused_604_; lean_object* v_unused_605_; 
v_unused_602_ = lean_ctor_get(v_lchild_554_, 3);
lean_dec(v_unused_602_);
v_unused_603_ = lean_ctor_get(v_lchild_554_, 2);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_lchild_554_, 1);
lean_dec(v_unused_604_);
v_unused_605_ = lean_ctor_get(v_lchild_554_, 0);
lean_dec(v_unused_605_);
v___x_596_ = v_lchild_554_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_dec(v_lchild_554_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 3, v___x_552_);
lean_ctor_set(v___x_596_, 2, v_val_467_);
lean_ctor_set(v___x_596_, 1, v_key_466_);
lean_ctor_set(v___x_596_, 0, v_lchild_465_);
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_lchild_465_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_key_466_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_val_467_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v___x_552_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*4, v_color_443_);
return v___x_599_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_557_) == 1)
{
uint8_t v_color_606_; 
v_color_606_ = lean_ctor_get_uint8(v_rchild_557_, sizeof(void*)*4);
if (v_color_606_ == 0)
{
lean_object* v_lchild_607_; lean_object* v_key_608_; lean_object* v_val_609_; lean_object* v_rchild_610_; 
lean_dec_ref(v___x_552_);
v_lchild_607_ = lean_ctor_get(v_rchild_557_, 0);
lean_inc(v_lchild_607_);
v_key_608_ = lean_ctor_get(v_rchild_557_, 1);
lean_inc(v_key_608_);
v_val_609_ = lean_ctor_get(v_rchild_557_, 2);
lean_inc(v_val_609_);
v_rchild_610_ = lean_ctor_get(v_rchild_557_, 3);
lean_inc(v_rchild_610_);
lean_dec_ref(v_rchild_557_);
v_a_559_ = v_lchild_465_;
v_kx_560_ = v_key_466_;
v_vx_561_ = v_val_467_;
v_b_562_ = v_lchild_554_;
v_ky_563_ = v_key_555_;
v_vy_564_ = v_val_556_;
v_c_565_ = v_lchild_607_;
v_kz_566_ = v_key_608_;
v_vz_567_ = v_val_609_;
v_d_568_ = v_rchild_610_;
goto v___jp_558_;
}
else
{
lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_val_556_);
lean_dec(v_key_555_);
lean_dec(v_lchild_554_);
lean_del_object(v___x_470_);
v_isSharedCheck_617_ = !lean_is_exclusive(v_rchild_557_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; 
v_unused_618_ = lean_ctor_get(v_rchild_557_, 3);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_rchild_557_, 2);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_rchild_557_, 1);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_rchild_557_, 0);
lean_dec(v_unused_621_);
v___x_612_ = v_rchild_557_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_dec(v_rchild_557_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 3, v___x_552_);
lean_ctor_set(v___x_612_, 2, v_val_467_);
lean_ctor_set(v___x_612_, 1, v_key_466_);
lean_ctor_set(v___x_612_, 0, v_lchild_465_);
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_lchild_465_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_key_466_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_val_467_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v___x_552_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*4, v_color_443_);
return v___x_615_;
}
}
}
}
else
{
lean_object* v___x_622_; 
lean_dec(v_rchild_557_);
lean_dec(v_val_556_);
lean_dec(v_key_555_);
lean_dec(v_lchild_554_);
lean_del_object(v___x_470_);
v___x_622_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_622_, 0, v_lchild_465_);
lean_ctor_set(v___x_622_, 1, v_key_466_);
lean_ctor_set(v___x_622_, 2, v_val_467_);
lean_ctor_set(v___x_622_, 3, v___x_552_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*4, v_color_443_);
return v___x_622_;
}
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_rchild_557_);
lean_dec(v_val_556_);
lean_dec(v_key_555_);
lean_dec(v_lchild_554_);
lean_del_object(v___x_470_);
v___x_623_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_623_, 0, v_lchild_465_);
lean_ctor_set(v___x_623_, 1, v_key_466_);
lean_ctor_set(v___x_623_, 2, v_val_467_);
lean_ctor_set(v___x_623_, 3, v___x_552_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*4, v_color_443_);
return v___x_623_;
}
v___jp_558_:
{
lean_object* v___x_570_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 3, v_b_562_);
lean_ctor_set(v___x_470_, 2, v_vx_561_);
lean_ctor_set(v___x_470_, 1, v_kx_560_);
lean_ctor_set(v___x_470_, 0, v_a_559_);
v___x_570_ = v___x_470_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_559_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_kx_560_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_vx_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_b_562_);
lean_ctor_set_uint8(v_reuseFailAlloc_573_, sizeof(void*)*4, v_color_443_);
v___x_570_ = v_reuseFailAlloc_573_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_571_, 0, v_c_565_);
lean_ctor_set(v___x_571_, 1, v_kz_566_);
lean_ctor_set(v___x_571_, 2, v_vz_567_);
lean_ctor_set(v___x_571_, 3, v_d_568_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*4, v_color_443_);
v___x_572_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v_ky_563_);
lean_ctor_set(v___x_572_, 2, v_vy_564_);
lean_ctor_set(v___x_572_, 3, v___x_571_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*4, v_color_553_);
return v___x_572_;
}
}
}
else
{
lean_object* v___x_625_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 3, v___x_552_);
v___x_625_ = v___x_470_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_lchild_465_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_key_466_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_val_467_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v___x_552_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*4, v_color_443_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(lean_object* v_cmp_628_, lean_object* v_t_629_, lean_object* v_k_630_, lean_object* v_v_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = l_Lean_RBNode_isRed___redArg(v_t_629_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_628_, v_t_629_, v_k_630_, v_v_631_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_628_, v_t_629_, v_k_630_, v_v_631_);
v___x_635_ = l_Lean_RBNode_setBlack___redArg(v___x_634_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(lean_object* v_cmp_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
if (lean_obj_tag(v_x_638_) == 0)
{
lean_dec_ref(v_cmp_636_);
return v_x_637_;
}
else
{
lean_object* v_head_639_; lean_object* v_tail_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_head_639_ = lean_ctor_get(v_x_638_, 0);
lean_inc(v_head_639_);
v_tail_640_ = lean_ctor_get(v_x_638_, 1);
lean_inc(v_tail_640_);
lean_dec_ref(v_x_638_);
v___x_641_ = lean_box(0);
lean_inc_ref(v_cmp_636_);
v___x_642_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_636_, v_x_637_, v_head_639_, v___x_641_);
v_x_637_ = v___x_642_;
v_x_638_ = v_tail_640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList___redArg(lean_object* v_l_644_, lean_object* v_cmp_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_box(0);
v___x_647_ = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(v_cmp_645_, v___x_646_, v_l_644_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList(lean_object* v_00_u03b1_648_, lean_object* v_l_649_, lean_object* v_cmp_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_RBTree_fromList___redArg(v_l_649_, v_cmp_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0(lean_object* v_00_u03b1_652_, lean_object* v_cmp_653_, lean_object* v_00_u03b2_654_, lean_object* v_t_655_, lean_object* v_k_656_, lean_object* v_v_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_653_, v_t_655_, v_k_656_, v_v_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1(lean_object* v_00_u03b1_659_, lean_object* v_cmp_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(v_cmp_660_, v_x_661_, v_x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0(lean_object* v_00_u03b1_664_, lean_object* v_cmp_665_, lean_object* v_00_u03b2_666_, lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_665_, v_x_667_, v_x_668_, v_x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(lean_object* v_cmp_671_, lean_object* v_as_672_, size_t v_i_673_, size_t v_stop_674_, lean_object* v_b_675_){
_start:
{
uint8_t v___x_676_; 
v___x_676_ = lean_usize_dec_eq(v_i_673_, v_stop_674_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; size_t v___x_680_; size_t v___x_681_; 
v___x_677_ = lean_array_uget_borrowed(v_as_672_, v_i_673_);
v___x_678_ = lean_box(0);
lean_inc(v___x_677_);
lean_inc_ref(v_cmp_671_);
v___x_679_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_671_, v_b_675_, v___x_677_, v___x_678_);
v___x_680_ = ((size_t)1ULL);
v___x_681_ = lean_usize_add(v_i_673_, v___x_680_);
v_i_673_ = v___x_681_;
v_b_675_ = v___x_679_;
goto _start;
}
else
{
lean_dec_ref(v_cmp_671_);
return v_b_675_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg___boxed(lean_object* v_cmp_683_, lean_object* v_as_684_, lean_object* v_i_685_, lean_object* v_stop_686_, lean_object* v_b_687_){
_start:
{
size_t v_i_boxed_688_; size_t v_stop_boxed_689_; lean_object* v_res_690_; 
v_i_boxed_688_ = lean_unbox_usize(v_i_685_);
lean_dec(v_i_685_);
v_stop_boxed_689_ = lean_unbox_usize(v_stop_686_);
lean_dec(v_stop_686_);
v_res_690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_683_, v_as_684_, v_i_boxed_688_, v_stop_boxed_689_, v_b_687_);
lean_dec_ref(v_as_684_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg(lean_object* v_l_691_, lean_object* v_cmp_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_693_ = lean_box(0);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_array_get_size(v_l_691_);
v___x_696_ = lean_nat_dec_lt(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_dec_ref(v_cmp_692_);
return v___x_693_;
}
else
{
uint8_t v___x_697_; 
v___x_697_ = lean_nat_dec_le(v___x_695_, v___x_695_);
if (v___x_697_ == 0)
{
if (v___x_696_ == 0)
{
lean_dec_ref(v_cmp_692_);
return v___x_693_;
}
else
{
size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v___x_698_ = ((size_t)0ULL);
v___x_699_ = lean_usize_of_nat(v___x_695_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_692_, v_l_691_, v___x_698_, v___x_699_, v___x_693_);
return v___x_700_;
}
}
else
{
size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((size_t)0ULL);
v___x_702_ = lean_usize_of_nat(v___x_695_);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_692_, v_l_691_, v___x_701_, v___x_702_, v___x_693_);
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg___boxed(lean_object* v_l_704_, lean_object* v_cmp_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_RBTree_fromArray___redArg(v_l_704_, v_cmp_705_);
lean_dec_ref(v_l_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray(lean_object* v_00_u03b1_707_, lean_object* v_l_708_, lean_object* v_cmp_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_RBTree_fromArray___redArg(v_l_708_, v_cmp_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___boxed(lean_object* v_00_u03b1_711_, lean_object* v_l_712_, lean_object* v_cmp_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_RBTree_fromArray(v_00_u03b1_711_, v_l_712_, v_cmp_713_);
lean_dec_ref(v_l_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(lean_object* v_00_u03b1_715_, lean_object* v_cmp_716_, lean_object* v_as_717_, size_t v_i_718_, size_t v_stop_719_, lean_object* v_b_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_716_, v_as_717_, v_i_718_, v_stop_719_, v_b_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___boxed(lean_object* v_00_u03b1_722_, lean_object* v_cmp_723_, lean_object* v_as_724_, lean_object* v_i_725_, lean_object* v_stop_726_, lean_object* v_b_727_){
_start:
{
size_t v_i_boxed_728_; size_t v_stop_boxed_729_; lean_object* v_res_730_; 
v_i_boxed_728_ = lean_unbox_usize(v_i_725_);
lean_dec(v_i_725_);
v_stop_boxed_729_ = lean_unbox_usize(v_stop_726_);
lean_dec(v_stop_726_);
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(v_00_u03b1_722_, v_cmp_723_, v_as_724_, v_i_boxed_728_, v_stop_boxed_729_, v_b_727_);
lean_dec_ref(v_as_724_);
return v_res_730_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_all___redArg___lam__0(lean_object* v_p_731_, lean_object* v_a_732_, lean_object* v_x_733_){
_start:
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_apply_1(v_p_731_, v_a_732_);
v___x_735_ = lean_unbox(v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___lam__0___boxed(lean_object* v_p_736_, lean_object* v_a_737_, lean_object* v_x_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Lean_RBTree_all___redArg___lam__0(v_p_736_, v_a_737_, v_x_738_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_all___redArg(lean_object* v_t_741_, lean_object* v_p_742_){
_start:
{
lean_object* v___f_743_; uint8_t v___x_744_; 
v___f_743_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_743_, 0, v_p_742_);
v___x_744_ = l_Lean_RBNode_all___redArg(v___f_743_, v_t_741_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___boxed(lean_object* v_t_745_, lean_object* v_p_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l_Lean_RBTree_all___redArg(v_t_745_, v_p_746_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_all(lean_object* v_00_u03b1_749_, lean_object* v_cmp_750_, lean_object* v_t_751_, lean_object* v_p_752_){
_start:
{
lean_object* v___f_753_; uint8_t v___x_754_; 
v___f_753_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_753_, 0, v_p_752_);
v___x_754_ = l_Lean_RBNode_all___redArg(v___f_753_, v_t_751_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___boxed(lean_object* v_00_u03b1_755_, lean_object* v_cmp_756_, lean_object* v_t_757_, lean_object* v_p_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Lean_RBTree_all(v_00_u03b1_755_, v_cmp_756_, v_t_757_, v_p_758_);
lean_dec_ref(v_cmp_756_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_any___redArg(lean_object* v_t_761_, lean_object* v_p_762_){
_start:
{
lean_object* v___f_763_; uint8_t v___x_764_; 
v___f_763_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_763_, 0, v_p_762_);
v___x_764_ = l_Lean_RBNode_any___redArg(v___f_763_, v_t_761_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_any___redArg___boxed(lean_object* v_t_765_, lean_object* v_p_766_){
_start:
{
uint8_t v_res_767_; lean_object* v_r_768_; 
v_res_767_ = l_Lean_RBTree_any___redArg(v_t_765_, v_p_766_);
v_r_768_ = lean_box(v_res_767_);
return v_r_768_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_any(lean_object* v_00_u03b1_769_, lean_object* v_cmp_770_, lean_object* v_t_771_, lean_object* v_p_772_){
_start:
{
lean_object* v___f_773_; uint8_t v___x_774_; 
v___f_773_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_773_, 0, v_p_772_);
v___x_774_ = l_Lean_RBNode_any___redArg(v___f_773_, v_t_771_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_any___boxed(lean_object* v_00_u03b1_775_, lean_object* v_cmp_776_, lean_object* v_t_777_, lean_object* v_p_778_){
_start:
{
uint8_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l_Lean_RBTree_any(v_00_u03b1_775_, v_cmp_776_, v_t_777_, v_p_778_);
lean_dec_ref(v_cmp_776_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(lean_object* v_cmp_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_object* v___x_784_; 
lean_dec(v_x_783_);
lean_dec_ref(v_cmp_781_);
v___x_784_ = lean_box(0);
return v___x_784_;
}
else
{
lean_object* v_lchild_785_; lean_object* v_key_786_; lean_object* v_val_787_; lean_object* v_rchild_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_lchild_785_ = lean_ctor_get(v_x_782_, 0);
lean_inc(v_lchild_785_);
v_key_786_ = lean_ctor_get(v_x_782_, 1);
lean_inc_n(v_key_786_, 2);
v_val_787_ = lean_ctor_get(v_x_782_, 2);
lean_inc(v_val_787_);
v_rchild_788_ = lean_ctor_get(v_x_782_, 3);
lean_inc(v_rchild_788_);
lean_dec_ref(v_x_782_);
lean_inc_ref(v_cmp_781_);
lean_inc(v_x_783_);
v___x_789_ = lean_apply_2(v_cmp_781_, v_x_783_, v_key_786_);
v___x_790_ = lean_unbox(v___x_789_);
switch(v___x_790_)
{
case 0:
{
lean_dec(v_rchild_788_);
lean_dec(v_val_787_);
lean_dec(v_key_786_);
v_x_782_ = v_lchild_785_;
goto _start;
}
case 1:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec(v_rchild_788_);
lean_dec(v_lchild_785_);
lean_dec(v_x_783_);
lean_dec_ref(v_cmp_781_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v_key_786_);
lean_ctor_set(v___x_792_, 1, v_val_787_);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
default: 
{
lean_dec(v_val_787_);
lean_dec(v_key_786_);
lean_dec(v_lchild_785_);
v_x_782_ = v_rchild_788_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(lean_object* v_t_u2082_795_, lean_object* v_cmp_796_, lean_object* v_x_797_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
uint8_t v___x_798_; 
lean_dec_ref(v_cmp_796_);
lean_dec(v_t_u2082_795_);
v___x_798_ = 1;
return v___x_798_;
}
else
{
lean_object* v_lchild_799_; lean_object* v_key_800_; lean_object* v_rchild_801_; lean_object* v___x_802_; 
v_lchild_799_ = lean_ctor_get(v_x_797_, 0);
lean_inc(v_lchild_799_);
v_key_800_ = lean_ctor_get(v_x_797_, 1);
lean_inc(v_key_800_);
v_rchild_801_ = lean_ctor_get(v_x_797_, 3);
lean_inc(v_rchild_801_);
lean_dec_ref(v_x_797_);
lean_inc(v_t_u2082_795_);
lean_inc_ref(v_cmp_796_);
v___x_802_ = l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(v_cmp_796_, v_t_u2082_795_, v_key_800_);
if (lean_obj_tag(v___x_802_) == 0)
{
uint8_t v___x_803_; 
lean_dec(v_rchild_801_);
lean_dec(v_lchild_799_);
lean_dec_ref(v_cmp_796_);
lean_dec(v_t_u2082_795_);
v___x_803_ = 0;
return v___x_803_;
}
else
{
uint8_t v___x_804_; 
lean_dec_ref(v___x_802_);
lean_inc_ref(v_cmp_796_);
lean_inc(v_t_u2082_795_);
v___x_804_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_795_, v_cmp_796_, v_lchild_799_);
if (v___x_804_ == 0)
{
lean_dec(v_rchild_801_);
lean_dec_ref(v_cmp_796_);
lean_dec(v_t_u2082_795_);
return v___x_804_;
}
else
{
v_x_797_ = v_rchild_801_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg___boxed(lean_object* v_t_u2082_806_, lean_object* v_cmp_807_, lean_object* v_x_808_){
_start:
{
uint8_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_806_, v_cmp_807_, v_x_808_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_subset___redArg(lean_object* v_cmp_811_, lean_object* v_t_u2081_812_, lean_object* v_t_u2082_813_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_813_, v_cmp_811_, v_t_u2081_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___redArg___boxed(lean_object* v_cmp_815_, lean_object* v_t_u2081_816_, lean_object* v_t_u2082_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l_Lean_RBTree_subset___redArg(v_cmp_815_, v_t_u2081_816_, v_t_u2082_817_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_subset(lean_object* v_00_u03b1_820_, lean_object* v_cmp_821_, lean_object* v_t_u2081_822_, lean_object* v_t_u2082_823_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_823_, v_cmp_821_, v_t_u2081_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___boxed(lean_object* v_00_u03b1_825_, lean_object* v_cmp_826_, lean_object* v_t_u2081_827_, lean_object* v_t_u2082_828_){
_start:
{
uint8_t v_res_829_; lean_object* v_r_830_; 
v_res_829_ = l_Lean_RBTree_subset(v_00_u03b1_825_, v_cmp_826_, v_t_u2081_827_, v_t_u2082_828_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0(lean_object* v_00_u03b1_831_, lean_object* v_cmp_832_, lean_object* v_00_u03b2_833_, lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(v_cmp_832_, v_x_834_, v_x_835_);
return v___x_836_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(lean_object* v_00_u03b1_837_, lean_object* v_t_u2082_838_, lean_object* v_cmp_839_, lean_object* v_x_840_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_838_, v_cmp_839_, v_x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___boxed(lean_object* v_00_u03b1_842_, lean_object* v_t_u2082_843_, lean_object* v_cmp_844_, lean_object* v_x_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(v_00_u03b1_842_, v_t_u2082_843_, v_cmp_844_, v_x_845_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_seteq___redArg(lean_object* v_cmp_848_, lean_object* v_t_u2081_849_, lean_object* v_t_u2082_850_){
_start:
{
uint8_t v___x_851_; 
lean_inc(v_t_u2081_849_);
lean_inc_ref(v_cmp_848_);
lean_inc(v_t_u2082_850_);
v___x_851_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_850_, v_cmp_848_, v_t_u2081_849_);
if (v___x_851_ == 0)
{
lean_dec(v_t_u2082_850_);
lean_dec(v_t_u2081_849_);
lean_dec_ref(v_cmp_848_);
return v___x_851_;
}
else
{
uint8_t v___x_852_; 
v___x_852_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2081_849_, v_cmp_848_, v_t_u2082_850_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___redArg___boxed(lean_object* v_cmp_853_, lean_object* v_t_u2081_854_, lean_object* v_t_u2082_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Lean_RBTree_seteq___redArg(v_cmp_853_, v_t_u2081_854_, v_t_u2082_855_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_seteq(lean_object* v_00_u03b1_858_, lean_object* v_cmp_859_, lean_object* v_t_u2081_860_, lean_object* v_t_u2082_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = l_Lean_RBTree_seteq___redArg(v_cmp_859_, v_t_u2081_860_, v_t_u2082_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___boxed(lean_object* v_00_u03b1_863_, lean_object* v_cmp_864_, lean_object* v_t_u2081_865_, lean_object* v_t_u2082_866_){
_start:
{
uint8_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = l_Lean_RBTree_seteq(v_00_u03b1_863_, v_cmp_864_, v_t_u2081_865_, v_t_u2082_866_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(lean_object* v_cmp_869_, lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_dec_ref(v_cmp_869_);
return v_x_870_;
}
else
{
lean_object* v_lchild_872_; lean_object* v_key_873_; lean_object* v_rchild_874_; lean_object* v_val_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_lchild_872_ = lean_ctor_get(v_x_871_, 0);
lean_inc(v_lchild_872_);
v_key_873_ = lean_ctor_get(v_x_871_, 1);
lean_inc(v_key_873_);
v_rchild_874_ = lean_ctor_get(v_x_871_, 3);
lean_inc(v_rchild_874_);
lean_dec_ref(v_x_871_);
lean_inc_ref_n(v_cmp_869_, 2);
v_val_875_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(v_cmp_869_, v_x_870_, v_lchild_872_);
v___x_876_ = lean_box(0);
v___x_877_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_869_, v_val_875_, v_key_873_, v___x_876_);
v_x_870_ = v___x_877_;
v_x_871_ = v_rchild_874_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_union___redArg(lean_object* v_cmp_879_, lean_object* v_t_u2081_880_, lean_object* v_t_u2082_881_){
_start:
{
if (lean_obj_tag(v_t_u2081_880_) == 0)
{
lean_dec_ref(v_cmp_879_);
return v_t_u2082_881_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(v_cmp_879_, v_t_u2081_880_, v_t_u2082_881_);
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_union(lean_object* v_00_u03b1_883_, lean_object* v_cmp_884_, lean_object* v_t_u2081_885_, lean_object* v_t_u2082_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_RBTree_union___redArg(v_cmp_884_, v_t_u2081_885_, v_t_u2082_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0(lean_object* v_00_u03b1_888_, lean_object* v_cmp_889_, lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(v_cmp_889_, v_x_890_, v_x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(lean_object* v_cmp_893_, lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_895_) == 0)
{
lean_dec(v_x_894_);
lean_dec_ref(v_cmp_893_);
return v_x_895_;
}
else
{
lean_object* v_lchild_896_; lean_object* v_key_897_; lean_object* v_val_898_; lean_object* v_rchild_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_922_; 
v_lchild_896_ = lean_ctor_get(v_x_895_, 0);
v_key_897_ = lean_ctor_get(v_x_895_, 1);
v_val_898_ = lean_ctor_get(v_x_895_, 2);
v_rchild_899_ = lean_ctor_get(v_x_895_, 3);
v_isSharedCheck_922_ = !lean_is_exclusive(v_x_895_);
if (v_isSharedCheck_922_ == 0)
{
v___x_901_ = v_x_895_;
v_isShared_902_ = v_isSharedCheck_922_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_rchild_899_);
lean_inc(v_val_898_);
lean_inc(v_key_897_);
lean_inc(v_lchild_896_);
lean_dec(v_x_895_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_922_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; uint8_t v___x_904_; 
lean_inc_ref(v_cmp_893_);
lean_inc(v_key_897_);
lean_inc(v_x_894_);
v___x_903_ = lean_apply_2(v_cmp_893_, v_x_894_, v_key_897_);
v___x_904_ = lean_unbox(v___x_903_);
switch(v___x_904_)
{
case 0:
{
uint8_t v___x_905_; 
v___x_905_ = l_Lean_RBNode_isBlack___redArg(v_lchild_896_);
if (v___x_905_ == 0)
{
uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_906_ = 0;
v___x_907_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_893_, v_x_894_, v_lchild_896_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_907_);
v___x_909_ = v___x_901_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_key_897_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_val_898_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_rchild_899_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_ctor_set_uint8(v___x_909_, sizeof(void*)*4, v___x_906_);
return v___x_909_;
}
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_del_object(v___x_901_);
v___x_911_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_893_, v_x_894_, v_lchild_896_);
v___x_912_ = l_Lean_RBNode_balLeft___redArg(v___x_911_, v_key_897_, v_val_898_, v_rchild_899_);
return v___x_912_;
}
}
case 1:
{
lean_object* v___x_913_; 
lean_del_object(v___x_901_);
lean_dec(v_val_898_);
lean_dec(v_key_897_);
lean_dec(v_x_894_);
lean_dec_ref(v_cmp_893_);
v___x_913_ = l_Lean_RBNode_appendTrees___redArg(v_lchild_896_, v_rchild_899_);
return v___x_913_;
}
default: 
{
uint8_t v___x_914_; 
v___x_914_ = l_Lean_RBNode_isBlack___redArg(v_rchild_899_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_915_ = 0;
v___x_916_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_893_, v_x_894_, v_rchild_899_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 3, v___x_916_);
v___x_918_ = v___x_901_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_lchild_896_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_key_897_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_val_898_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*4, v___x_915_);
return v___x_918_;
}
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; 
lean_del_object(v___x_901_);
v___x_920_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_893_, v_x_894_, v_rchild_899_);
v___x_921_ = l_Lean_RBNode_balRight___redArg(v_lchild_896_, v_key_897_, v_val_898_, v___x_920_);
return v___x_921_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(lean_object* v_cmp_923_, lean_object* v_x_924_, lean_object* v_t_925_){
_start:
{
lean_object* v_t_926_; lean_object* v___x_927_; 
v_t_926_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_923_, v_x_924_, v_t_925_);
v___x_927_ = l_Lean_RBNode_setBlack___redArg(v_t_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(lean_object* v_cmp_928_, lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
if (lean_obj_tag(v_x_930_) == 0)
{
lean_dec_ref(v_cmp_928_);
return v_x_929_;
}
else
{
lean_object* v_lchild_931_; lean_object* v_key_932_; lean_object* v_rchild_933_; lean_object* v_val_934_; lean_object* v___x_935_; 
v_lchild_931_ = lean_ctor_get(v_x_930_, 0);
lean_inc(v_lchild_931_);
v_key_932_ = lean_ctor_get(v_x_930_, 1);
lean_inc(v_key_932_);
v_rchild_933_ = lean_ctor_get(v_x_930_, 3);
lean_inc(v_rchild_933_);
lean_dec_ref(v_x_930_);
lean_inc_ref_n(v_cmp_928_, 2);
v_val_934_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_928_, v_x_929_, v_lchild_931_);
v___x_935_ = l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(v_cmp_928_, v_key_932_, v_val_934_);
v_x_929_ = v___x_935_;
v_x_930_ = v_rchild_933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_diff___redArg(lean_object* v_cmp_937_, lean_object* v_t_u2081_938_, lean_object* v_t_u2082_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_937_, v_t_u2081_938_, v_t_u2082_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_diff(lean_object* v_00_u03b1_941_, lean_object* v_cmp_942_, lean_object* v_t_u2081_943_, lean_object* v_t_u2082_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_942_, v_t_u2081_943_, v_t_u2082_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0(lean_object* v_00_u03b1_946_, lean_object* v_cmp_947_, lean_object* v_00_u03b2_948_, lean_object* v_x_949_, lean_object* v_t_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(v_cmp_947_, v_x_949_, v_t_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1(lean_object* v_00_u03b1_952_, lean_object* v_cmp_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_953_, v_x_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0(lean_object* v_00_u03b1_957_, lean_object* v_cmp_958_, lean_object* v_00_u03b2_959_, lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_958_, v_x_960_, v_x_961_);
return v___x_962_;
}
}
LEAN_EXPORT uint8_t l_Lean_RBTree_filter___redArg___lam__0(lean_object* v_f_963_, lean_object* v_a_964_, lean_object* v_x_965_){
_start:
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_apply_1(v_f_963_, v_a_964_);
v___x_967_ = lean_unbox(v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg___lam__0___boxed(lean_object* v_f_968_, lean_object* v_a_969_, lean_object* v_x_970_){
_start:
{
uint8_t v_res_971_; lean_object* v_r_972_; 
v_res_971_ = l_Lean_RBTree_filter___redArg___lam__0(v_f_968_, v_a_969_, v_x_970_);
v_r_972_ = lean_box(v_res_971_);
return v_r_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg(lean_object* v_cmp_973_, lean_object* v_f_974_, lean_object* v_m_975_){
_start:
{
lean_object* v___f_976_; lean_object* v___x_977_; 
v___f_976_ = lean_alloc_closure((void*)(l_Lean_RBTree_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_976_, 0, v_f_974_);
v___x_977_ = l_Lean_RBMap_filter___redArg(v_cmp_973_, v___f_976_, v_m_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter(lean_object* v_00_u03b1_978_, lean_object* v_cmp_979_, lean_object* v_f_980_, lean_object* v_m_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_RBTree_filter___redArg(v_cmp_979_, v_f_980_, v_m_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbtreeOf___redArg(lean_object* v_l_983_, lean_object* v_cmp_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_RBTree_fromList___redArg(v_l_983_, v_cmp_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbtreeOf(lean_object* v_00_u03b1_986_, lean_object* v_l_987_, lean_object* v_cmp_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_RBTree_fromList___redArg(v_l_987_, v_cmp_988_);
return v___x_989_;
}
}
lean_object* runtime_initialize_Lean_Data_RBMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_RBTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
