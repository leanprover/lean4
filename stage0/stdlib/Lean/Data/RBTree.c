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
lean_object* l_Lean_instInhabitedRBTree___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedRBTree___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Lean_instInhabitedRBTree___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_instInhabitedRBTree___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree(lean_object* v_00_u03b1_6_, lean_object* v_p_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedRBTree___boxed(lean_object* v_00_u03b1_9_, lean_object* v_p_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_instInhabitedRBTree(v_00_u03b1_9_, v_p_10_);
lean_dec_ref(v_p_10_);
return v_res_11_;
}
}
lean_object* l_Lean_mkRBTree___redArg(){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_box(0);
return v___x_13_;
}
}
LEAN_EXPORT void l_Lean_mkRBTree___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_14_;
v_res_14_ = l_Lean_mkRBTree___redArg();
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_Lean_mkRBTree___redArg___boxed(lean_object* v___dummy_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_mkRBTree___redArg();
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBTree(lean_object* v_00_u03b1_17_, lean_object* v_cmp_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(0);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRBTree___boxed(lean_object* v_00_u03b1_20_, lean_object* v_cmp_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_mkRBTree(v_00_u03b1_20_, v_cmp_21_);
lean_dec_ref(v_cmp_21_);
return v_res_22_;
}
}
lean_object* l_Lean_instEmptyCollectionRBTree___redArg(){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_box(0);
return v___x_24_;
}
}
LEAN_EXPORT void l_Lean_instEmptyCollectionRBTree___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_25_;
v_res_25_ = l_Lean_instEmptyCollectionRBTree___redArg();
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___redArg___boxed(lean_object* v___dummy_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_instEmptyCollectionRBTree___redArg();
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree(lean_object* v_00_u03b1_28_, lean_object* v_cmp_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_box(0);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionRBTree___boxed(lean_object* v_00_u03b1_31_, lean_object* v_cmp_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_instEmptyCollectionRBTree(v_00_u03b1_31_, v_cmp_32_);
lean_dec_ref(v_cmp_32_);
return v_res_33_;
}
}
lean_object* l_Lean_RBTree_empty___redArg(){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
LEAN_EXPORT void l_Lean_RBTree_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_36_;
v_res_36_ = l_Lean_RBTree_empty___redArg();
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_empty___redArg___boxed(lean_object* v___dummy_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_RBTree_empty___redArg();
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_empty(lean_object* v_00_u03b1_39_, lean_object* v_cmp_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_box(0);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_empty___boxed(lean_object* v_00_u03b1_42_, lean_object* v_cmp_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_RBTree_empty(v_00_u03b1_42_, v_cmp_43_);
lean_dec_ref(v_cmp_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg(lean_object* v_f_45_, lean_object* v_t_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_RBNode_depth___redArg(v_f_45_, v_t_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___redArg___boxed(lean_object* v_f_48_, lean_object* v_t_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_RBTree_depth___redArg(v_f_48_, v_t_49_);
lean_dec(v_t_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth(lean_object* v_00_u03b1_51_, lean_object* v_cmp_52_, lean_object* v_f_53_, lean_object* v_t_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_RBNode_depth___redArg(v_f_53_, v_t_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_depth___boxed(lean_object* v_00_u03b1_56_, lean_object* v_cmp_57_, lean_object* v_f_58_, lean_object* v_t_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_RBTree_depth(v_00_u03b1_56_, v_cmp_57_, v_f_58_, v_t_59_);
lean_dec(v_t_59_);
lean_dec_ref(v_cmp_57_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg___lam__0(lean_object* v_f_61_, lean_object* v_r_62_, lean_object* v_a_63_, lean_object* v_x_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_apply_2(v_f_61_, v_r_62_, v_a_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___redArg(lean_object* v_f_66_, lean_object* v_init_67_, lean_object* v_t_68_){
_start:
{
lean_object* v___f_69_; lean_object* v___x_70_; 
v___f_69_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_69_, 0, v_f_66_);
v___x_70_ = l_Lean_RBNode_fold___redArg(v___f_69_, v_init_67_, v_t_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold(lean_object* v_00_u03b1_71_, lean_object* v_00_u03b2_72_, lean_object* v_cmp_73_, lean_object* v_f_74_, lean_object* v_init_75_, lean_object* v_t_76_){
_start:
{
lean_object* v___f_77_; lean_object* v___x_78_; 
v___f_77_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_77_, 0, v_f_74_);
v___x_78_ = l_Lean_RBNode_fold___redArg(v___f_77_, v_init_75_, v_t_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fold___boxed(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_cmp_81_, lean_object* v_f_82_, lean_object* v_init_83_, lean_object* v_t_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_RBTree_fold(v_00_u03b1_79_, v_00_u03b2_80_, v_cmp_81_, v_f_82_, v_init_83_, v_t_84_);
lean_dec_ref(v_cmp_81_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___redArg(lean_object* v_f_86_, lean_object* v_init_87_, lean_object* v_t_88_){
_start:
{
lean_object* v___f_89_; lean_object* v___x_90_; 
v___f_89_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_89_, 0, v_f_86_);
v___x_90_ = l_Lean_RBNode_revFold___redArg(v___f_89_, v_init_87_, v_t_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_cmp_93_, lean_object* v_f_94_, lean_object* v_init_95_, lean_object* v_t_96_){
_start:
{
lean_object* v___f_97_; lean_object* v___x_98_; 
v___f_97_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_97_, 0, v_f_94_);
v___x_98_ = l_Lean_RBNode_revFold___redArg(v___f_97_, v_init_95_, v_t_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_revFold___boxed(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_cmp_101_, lean_object* v_f_102_, lean_object* v_init_103_, lean_object* v_t_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_RBTree_revFold(v_00_u03b1_99_, v_00_u03b2_100_, v_cmp_101_, v_f_102_, v_init_103_, v_t_104_);
lean_dec_ref(v_cmp_101_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___redArg(lean_object* v_inst_106_, lean_object* v_f_107_, lean_object* v_init_108_, lean_object* v_t_109_){
_start:
{
lean_object* v___f_110_; lean_object* v___x_111_; 
v___f_110_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_110_, 0, v_f_107_);
v___x_111_ = l_Lean_RBNode_foldM___redArg(v_inst_106_, v___f_110_, v_init_108_, v_t_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM(lean_object* v_00_u03b1_112_, lean_object* v_00_u03b2_113_, lean_object* v_cmp_114_, lean_object* v_m_115_, lean_object* v_inst_116_, lean_object* v_f_117_, lean_object* v_init_118_, lean_object* v_t_119_){
_start:
{
lean_object* v___f_120_; lean_object* v___x_121_; 
v___f_120_ = lean_alloc_closure((void*)(l_Lean_RBTree_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_120_, 0, v_f_117_);
v___x_121_ = l_Lean_RBNode_foldM___redArg(v_inst_116_, v___f_120_, v_init_118_, v_t_119_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_foldM___boxed(lean_object* v_00_u03b1_122_, lean_object* v_00_u03b2_123_, lean_object* v_cmp_124_, lean_object* v_m_125_, lean_object* v_inst_126_, lean_object* v_f_127_, lean_object* v_init_128_, lean_object* v_t_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_RBTree_foldM(v_00_u03b1_122_, v_00_u03b2_123_, v_cmp_124_, v_m_125_, v_inst_126_, v_f_127_, v_init_128_, v_t_129_);
lean_dec_ref(v_cmp_124_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg___lam__0(lean_object* v_f_131_, lean_object* v_r_132_, lean_object* v_a_133_, lean_object* v_x_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_apply_1(v_f_131_, v_a_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___redArg(lean_object* v_inst_136_, lean_object* v_f_137_, lean_object* v_t_138_){
_start:
{
lean_object* v___f_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___f_139_ = lean_alloc_closure((void*)(l_Lean_RBTree_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_139_, 0, v_f_137_);
v___x_140_ = lean_box(0);
v___x_141_ = l_Lean_RBNode_foldM___redArg(v_inst_136_, v___f_139_, v___x_140_, v_t_138_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM(lean_object* v_00_u03b1_142_, lean_object* v_cmp_143_, lean_object* v_m_144_, lean_object* v_inst_145_, lean_object* v_f_146_, lean_object* v_t_147_){
_start:
{
lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___f_148_ = lean_alloc_closure((void*)(l_Lean_RBTree_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_148_, 0, v_f_146_);
v___x_149_ = lean_box(0);
v___x_150_ = l_Lean_RBNode_foldM___redArg(v_inst_145_, v___f_148_, v___x_149_, v_t_147_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forM___boxed(lean_object* v_00_u03b1_151_, lean_object* v_cmp_152_, lean_object* v_m_153_, lean_object* v_inst_154_, lean_object* v_f_155_, lean_object* v_t_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_RBTree_forM(v_00_u03b1_151_, v_cmp_152_, v_m_153_, v_inst_154_, v_f_155_, v_t_156_);
lean_dec_ref(v_cmp_152_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__0(lean_object* v_f_158_, lean_object* v_a_159_, lean_object* v_x_160_, lean_object* v_acc_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_apply_2(v_f_158_, v_a_159_, v_acc_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg___lam__1(lean_object* v_toPure_163_, lean_object* v_____do__lift_164_){
_start:
{
lean_object* v_a_165_; lean_object* v___x_166_; 
v_a_165_ = lean_ctor_get(v_____do__lift_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref(v_____do__lift_164_);
v___x_166_ = lean_apply_2(v_toPure_163_, lean_box(0), v_a_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___redArg(lean_object* v_inst_167_, lean_object* v_t_168_, lean_object* v_init_169_, lean_object* v_f_170_){
_start:
{
lean_object* v_toApplicative_171_; lean_object* v_toBind_172_; lean_object* v_toPure_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___f_176_; lean_object* v___x_177_; 
v_toApplicative_171_ = lean_ctor_get(v_inst_167_, 0);
v_toBind_172_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_toBind_172_);
v_toPure_173_ = lean_ctor_get(v_toApplicative_171_, 1);
lean_inc(v_toPure_173_);
v___f_174_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_174_, 0, v_f_170_);
v___x_175_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_167_, v___f_174_, v_t_168_, v_init_169_);
v___f_176_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_176_, 0, v_toPure_173_);
v___x_177_ = lean_apply_4(v_toBind_172_, lean_box(0), lean_box(0), v___x_175_, v___f_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn(lean_object* v_00_u03b1_178_, lean_object* v_cmp_179_, lean_object* v_m_180_, lean_object* v_00_u03c3_181_, lean_object* v_inst_182_, lean_object* v_t_183_, lean_object* v_init_184_, lean_object* v_f_185_){
_start:
{
lean_object* v_toApplicative_186_; lean_object* v_toBind_187_; lean_object* v_toPure_188_; lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___f_191_; lean_object* v___x_192_; 
v_toApplicative_186_ = lean_ctor_get(v_inst_182_, 0);
v_toBind_187_ = lean_ctor_get(v_inst_182_, 1);
lean_inc(v_toBind_187_);
v_toPure_188_ = lean_ctor_get(v_toApplicative_186_, 1);
lean_inc(v_toPure_188_);
v___f_189_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_189_, 0, v_f_185_);
v___x_190_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_182_, v___f_189_, v_t_183_, v_init_184_);
v___f_191_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_191_, 0, v_toPure_188_);
v___x_192_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v___x_190_, v___f_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_forIn___boxed(lean_object* v_00_u03b1_193_, lean_object* v_cmp_194_, lean_object* v_m_195_, lean_object* v_00_u03c3_196_, lean_object* v_inst_197_, lean_object* v_t_198_, lean_object* v_init_199_, lean_object* v_f_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_RBTree_forIn(v_00_u03b1_193_, v_cmp_194_, v_m_195_, v_00_u03c3_196_, v_inst_197_, v_t_198_, v_init_199_, v_f_200_);
lean_dec_ref(v_cmp_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__0(lean_object* v___y_202_, lean_object* v_a_203_, lean_object* v_x_204_, lean_object* v_acc_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_apply_2(v___y_202_, v_a_203_, v_acc_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg___lam__2(lean_object* v_inst_207_, lean_object* v_00_u03b2_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_toApplicative_212_; lean_object* v_toBind_213_; lean_object* v_toPure_214_; lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v___f_217_; lean_object* v___x_218_; 
v_toApplicative_212_ = lean_ctor_get(v_inst_207_, 0);
v_toBind_213_ = lean_ctor_get(v_inst_207_, 1);
lean_inc(v_toBind_213_);
v_toPure_214_ = lean_ctor_get(v_toApplicative_212_, 1);
lean_inc(v_toPure_214_);
v___f_215_ = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_215_, 0, v___y_211_);
v___x_216_ = l___private_Lean_Data_RBMap_0__Lean_RBNode_forIn_visit(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_207_, v___f_215_, v___y_209_, v___y_210_);
v___f_217_ = lean_alloc_closure((void*)(l_Lean_RBTree_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_217_, 0, v_toPure_214_);
v___x_218_ = lean_apply_4(v_toBind_213_, lean_box(0), lean_box(0), v___x_216_, v___f_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___redArg(lean_object* v_inst_219_){
_start:
{
lean_object* v___f_220_; 
v___f_220_ = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_220_, 0, v_inst_219_);
return v___f_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad(lean_object* v_00_u03b1_221_, lean_object* v_cmp_222_, lean_object* v_m_223_, lean_object* v_inst_224_){
_start:
{
lean_object* v___f_225_; 
v___f_225_ = lean_alloc_closure((void*)(l_Lean_RBTree_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_225_, 0, v_inst_224_);
return v___f_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instForInOfMonad___boxed(lean_object* v_00_u03b1_226_, lean_object* v_cmp_227_, lean_object* v_m_228_, lean_object* v_inst_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_RBTree_instForInOfMonad(v_00_u03b1_226_, v_cmp_227_, v_m_228_, v_inst_229_);
lean_dec_ref(v_cmp_227_);
return v_res_230_;
}
}
uint8_t l_Lean_RBTree_isEmpty___redArg(lean_object* v_t_231_){
_start:
{
if (lean_obj_tag(v_t_231_) == 0)
{
uint8_t v___x_232_; 
v___x_232_ = 1;
return v___x_232_;
}
else
{
uint8_t v___x_233_; 
v___x_233_ = 0;
return v___x_233_;
}
}
}
LEAN_EXPORT void l_Lean_RBTree_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_231_ = stack[0].m_obj;
uint8_t v_res_234_;
v_res_234_ = l_Lean_RBTree_isEmpty___redArg(v_t_231_);
stack->m_num = v_res_234_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___redArg___boxed(lean_object* v_t_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = l_Lean_RBTree_isEmpty___redArg(v_t_235_);
lean_dec(v_t_235_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
uint8_t l_Lean_RBTree_isEmpty(lean_object* v_00_u03b1_238_, lean_object* v_cmp_239_, lean_object* v_t_240_){
_start:
{
if (lean_obj_tag(v_t_240_) == 0)
{
uint8_t v___x_241_; 
v___x_241_ = 1;
return v___x_241_;
}
else
{
uint8_t v___x_242_; 
v___x_242_ = 0;
return v___x_242_;
}
}
}
LEAN_EXPORT void l_Lean_RBTree_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_239_ = stack[1].m_obj;
lean_object* v_t_240_ = stack[2].m_obj;
uint8_t v_res_243_;
v_res_243_ = l_Lean_RBTree_isEmpty(lean_box(0), v_cmp_239_, v_t_240_);
stack->m_num = v_res_243_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_isEmpty___boxed(lean_object* v_00_u03b1_244_, lean_object* v_cmp_245_, lean_object* v_t_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Lean_RBTree_isEmpty(v_00_u03b1_244_, v_cmp_245_, v_t_246_);
lean_dec(v_t_246_);
lean_dec_ref(v_cmp_245_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg___lam__0(lean_object* v_r_249_, lean_object* v_a_250_, lean_object* v_x_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v_a_250_);
lean_ctor_set(v___x_252_, 1, v_r_249_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___redArg(lean_object* v_t_254_){
_start:
{
lean_object* v___f_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___f_255_ = ((lean_object*)(l_Lean_RBTree_toList___redArg___closed__0));
v___x_256_ = lean_box(0);
v___x_257_ = l_Lean_RBNode_revFold___redArg(v___f_255_, v___x_256_, v_t_254_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList(lean_object* v_00_u03b1_258_, lean_object* v_cmp_259_, lean_object* v_t_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_RBTree_toList___redArg(v_t_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___boxed(lean_object* v_00_u03b1_262_, lean_object* v_cmp_263_, lean_object* v_t_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_RBTree_toList(v_00_u03b1_262_, v_cmp_263_, v_t_264_);
lean_dec_ref(v_cmp_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg___lam__0(lean_object* v_r_266_, lean_object* v_a_267_, lean_object* v_x_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_array_push(v_r_266_, v_a_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___redArg(lean_object* v_t_273_){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___f_274_ = ((lean_object*)(l_Lean_RBTree_toArray___redArg___closed__0));
v___x_275_ = ((lean_object*)(l_Lean_RBTree_toArray___redArg___closed__1));
v___x_276_ = l_Lean_RBNode_fold___redArg(v___f_274_, v___x_275_, v_t_273_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray(lean_object* v_00_u03b1_277_, lean_object* v_cmp_278_, lean_object* v_t_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_RBTree_toArray___redArg(v_t_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___boxed(lean_object* v_00_u03b1_281_, lean_object* v_cmp_282_, lean_object* v_t_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_RBTree_toArray(v_00_u03b1_281_, v_cmp_282_, v_t_283_);
lean_dec_ref(v_cmp_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg(lean_object* v_t_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_RBNode_min___redArg(v_t_285_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_box(0);
return v___x_287_;
}
else
{
lean_object* v_val_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_296_; 
v_val_288_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_296_ == 0)
{
v___x_290_ = v___x_286_;
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_val_288_);
lean_dec(v___x_286_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_fst_292_; lean_object* v___x_294_; 
v_fst_292_ = lean_ctor_get(v_val_288_, 0);
lean_inc(v_fst_292_);
lean_dec(v_val_288_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_fst_292_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_fst_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min___redArg___boxed(lean_object* v_t_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_RBTree_min___redArg(v_t_297_);
lean_dec(v_t_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min(lean_object* v_00_u03b1_299_, lean_object* v_cmp_300_, lean_object* v_t_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_RBNode_min___redArg(v_t_301_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v___x_303_; 
v___x_303_ = lean_box(0);
return v___x_303_;
}
else
{
lean_object* v_val_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_312_; 
v_val_304_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_312_ == 0)
{
v___x_306_ = v___x_302_;
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_val_304_);
lean_dec(v___x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_fst_308_; lean_object* v___x_310_; 
v_fst_308_ = lean_ctor_get(v_val_304_, 0);
lean_inc(v_fst_308_);
lean_dec(v_val_304_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v_fst_308_);
v___x_310_ = v___x_306_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_fst_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_min___boxed(lean_object* v_00_u03b1_313_, lean_object* v_cmp_314_, lean_object* v_t_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_RBTree_min(v_00_u03b1_313_, v_cmp_314_, v_t_315_);
lean_dec(v_t_315_);
lean_dec_ref(v_cmp_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg(lean_object* v_t_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_RBNode_max___redArg(v_t_317_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v___x_319_; 
v___x_319_ = lean_box(0);
return v___x_319_;
}
else
{
lean_object* v_val_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_328_; 
v_val_320_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_328_ == 0)
{
v___x_322_ = v___x_318_;
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_val_320_);
lean_dec(v___x_318_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_fst_324_; lean_object* v___x_326_; 
v_fst_324_ = lean_ctor_get(v_val_320_, 0);
lean_inc(v_fst_324_);
lean_dec(v_val_320_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v_fst_324_);
v___x_326_ = v___x_322_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_fst_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max___redArg___boxed(lean_object* v_t_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_RBTree_max___redArg(v_t_329_);
lean_dec(v_t_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max(lean_object* v_00_u03b1_331_, lean_object* v_cmp_332_, lean_object* v_t_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_RBNode_max___redArg(v_t_333_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v___x_335_; 
v___x_335_ = lean_box(0);
return v___x_335_;
}
else
{
lean_object* v_val_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_344_; 
v_val_336_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_344_ == 0)
{
v___x_338_ = v___x_334_;
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_val_336_);
lean_dec(v___x_334_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v_fst_340_; lean_object* v___x_342_; 
v_fst_340_ = lean_ctor_get(v_val_336_, 0);
lean_inc(v_fst_340_);
lean_dec(v_val_336_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v_fst_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_fst_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_max___boxed(lean_object* v_00_u03b1_345_, lean_object* v_cmp_346_, lean_object* v_t_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_RBTree_max(v_00_u03b1_345_, v_cmp_346_, v_t_347_);
lean_dec(v_t_347_);
lean_dec_ref(v_cmp_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0(lean_object* v_inst_352_, lean_object* v_t_353_, lean_object* v_prec_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_355_ = ((lean_object*)(l_Lean_RBTree_instRepr___redArg___lam__0___closed__1));
v___x_356_ = l_Lean_RBTree_toList___redArg(v_t_353_);
v___x_357_ = l_List_repr___redArg(v_inst_352_, v___x_356_);
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_355_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = l_Repr_addAppParen(v___x_358_, v_prec_354_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg___lam__0___boxed(lean_object* v_inst_360_, lean_object* v_t_361_, lean_object* v_prec_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_RBTree_instRepr___redArg___lam__0(v_inst_360_, v_t_361_, v_prec_362_);
lean_dec(v_prec_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___redArg(lean_object* v_inst_364_){
_start:
{
lean_object* v___f_365_; 
v___f_365_ = lean_alloc_closure((void*)(l_Lean_RBTree_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_365_, 0, v_inst_364_);
return v___f_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr(lean_object* v_00_u03b1_366_, lean_object* v_cmp_367_, lean_object* v_inst_368_){
_start:
{
lean_object* v___f_369_; 
v___f_369_ = lean_alloc_closure((void*)(l_Lean_RBTree_instRepr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_369_, 0, v_inst_368_);
return v___f_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_instRepr___boxed(lean_object* v_00_u03b1_370_, lean_object* v_cmp_371_, lean_object* v_inst_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_RBTree_instRepr(v_00_u03b1_370_, v_cmp_371_, v_inst_372_);
lean_dec_ref(v_cmp_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_insert___redArg(lean_object* v_cmp_374_, lean_object* v_t_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_box(0);
v___x_378_ = l_Lean_RBNode_insert___redArg(v_cmp_374_, v_t_375_, v_a_376_, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_insert(lean_object* v_00_u03b1_379_, lean_object* v_cmp_380_, lean_object* v_t_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_box(0);
v___x_384_ = l_Lean_RBNode_insert___redArg(v_cmp_380_, v_t_381_, v_a_382_, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_erase___redArg(lean_object* v_cmp_385_, lean_object* v_t_386_, lean_object* v_a_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_RBNode_erase___redArg(v_cmp_385_, v_a_387_, v_t_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_erase(lean_object* v_00_u03b1_389_, lean_object* v_cmp_390_, lean_object* v_t_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_RBNode_erase___redArg(v_cmp_390_, v_a_392_, v_t_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___redArg(lean_object* v_cmp_394_, lean_object* v_x_395_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
lean_object* v___x_396_; 
lean_dec_ref(v_cmp_394_);
v___x_396_ = lean_box(0);
return v___x_396_;
}
else
{
lean_object* v_head_397_; lean_object* v_tail_398_; lean_object* v_val_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_head_397_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_head_397_);
v_tail_398_ = lean_ctor_get(v_x_395_, 1);
lean_inc(v_tail_398_);
lean_dec_ref_known(v_x_395_, 2);
lean_inc_ref(v_cmp_394_);
v_val_399_ = l_Lean_RBTree_ofList___redArg(v_cmp_394_, v_tail_398_);
v___x_400_ = lean_box(0);
v___x_401_ = l_Lean_RBNode_insert___redArg(v_cmp_394_, v_val_399_, v_head_397_, v___x_400_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList(lean_object* v_00_u03b1_402_, lean_object* v_cmp_403_, lean_object* v_x_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_RBTree_ofList___redArg(v_cmp_403_, v_x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f___redArg(lean_object* v_cmp_406_, lean_object* v_t_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_RBNode_findCore___redArg(v_cmp_406_, v_t_407_, v_a_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_box(0);
return v___x_410_;
}
else
{
lean_object* v_val_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_419_; 
v_val_411_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_419_ == 0)
{
v___x_413_ = v___x_409_;
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_val_411_);
lean_dec(v___x_409_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_419_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v_fst_415_; lean_object* v___x_417_; 
v_fst_415_ = lean_ctor_get(v_val_411_, 0);
lean_inc(v_fst_415_);
lean_dec(v_val_411_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v_fst_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_fst_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_find_x3f(lean_object* v_00_u03b1_420_, lean_object* v_cmp_421_, lean_object* v_t_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_RBNode_findCore___redArg(v_cmp_421_, v_t_422_, v_a_423_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_box(0);
return v___x_425_;
}
else
{
lean_object* v_val_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_434_; 
v_val_426_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_434_ == 0)
{
v___x_428_ = v___x_424_;
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_val_426_);
lean_dec(v___x_424_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_fst_430_; lean_object* v___x_432_; 
v_fst_430_ = lean_ctor_get(v_val_426_, 0);
lean_inc(v_fst_430_);
lean_dec(v_val_426_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v_fst_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_fst_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
uint8_t l_Lean_RBTree_contains___redArg(lean_object* v_cmp_435_, lean_object* v_t_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_RBNode_findCore___redArg(v_cmp_435_, v_t_436_, v_a_437_);
if (lean_obj_tag(v___x_438_) == 0)
{
uint8_t v___x_439_; 
v___x_439_ = 0;
return v___x_439_;
}
else
{
uint8_t v___x_440_; 
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = 1;
return v___x_440_;
}
}
}
LEAN_EXPORT void l_Lean_RBTree_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_435_ = stack[0].m_obj;
lean_object* v_t_436_ = stack[1].m_obj;
lean_object* v_a_437_ = stack[2].m_obj;
uint8_t v_res_441_;
v_res_441_ = l_Lean_RBTree_contains___redArg(v_cmp_435_, v_t_436_, v_a_437_);
stack->m_num = v_res_441_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___redArg___boxed(lean_object* v_cmp_442_, lean_object* v_t_443_, lean_object* v_a_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Lean_RBTree_contains___redArg(v_cmp_442_, v_t_443_, v_a_444_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
uint8_t l_Lean_RBTree_contains(lean_object* v_00_u03b1_447_, lean_object* v_cmp_448_, lean_object* v_t_449_, lean_object* v_a_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_RBNode_findCore___redArg(v_cmp_448_, v_t_449_, v_a_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
lean_dec_ref_known(v___x_451_, 1);
v___x_453_ = 1;
return v___x_453_;
}
}
}
LEAN_EXPORT void l_Lean_RBTree_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_448_ = stack[1].m_obj;
lean_object* v_t_449_ = stack[2].m_obj;
lean_object* v_a_450_ = stack[3].m_obj;
uint8_t v_res_454_;
v_res_454_ = l_Lean_RBTree_contains(lean_box(0), v_cmp_448_, v_t_449_, v_a_450_);
stack->m_num = v_res_454_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_contains___boxed(lean_object* v_00_u03b1_455_, lean_object* v_cmp_456_, lean_object* v_t_457_, lean_object* v_a_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_Lean_RBTree_contains(v_00_u03b1_455_, v_cmp_456_, v_t_457_, v_a_458_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(lean_object* v_cmp_461_, lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
uint8_t v___x_465_; lean_object* v___x_466_; 
lean_dec_ref(v_cmp_461_);
v___x_465_ = 0;
v___x_466_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_466_, 0, v_x_462_);
lean_ctor_set(v___x_466_, 1, v_x_463_);
lean_ctor_set(v___x_466_, 2, v_x_464_);
lean_ctor_set(v___x_466_, 3, v_x_462_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*4, v___x_465_);
return v___x_466_;
}
else
{
uint8_t v_color_467_; 
v_color_467_ = lean_ctor_get_uint8(v_x_462_, sizeof(void*)*4);
if (v_color_467_ == 0)
{
lean_object* v_lchild_468_; lean_object* v_key_469_; lean_object* v_val_470_; lean_object* v_rchild_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_488_; 
v_lchild_468_ = lean_ctor_get(v_x_462_, 0);
v_key_469_ = lean_ctor_get(v_x_462_, 1);
v_val_470_ = lean_ctor_get(v_x_462_, 2);
v_rchild_471_ = lean_ctor_get(v_x_462_, 3);
v_isSharedCheck_488_ = !lean_is_exclusive(v_x_462_);
if (v_isSharedCheck_488_ == 0)
{
v___x_473_ = v_x_462_;
v_isShared_474_ = v_isSharedCheck_488_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_rchild_471_);
lean_inc(v_val_470_);
lean_inc(v_key_469_);
lean_inc(v_lchild_468_);
lean_dec(v_x_462_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_488_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
lean_inc_ref(v_cmp_461_);
lean_inc(v_key_469_);
lean_inc(v_x_463_);
v___x_475_ = lean_apply_2(v_cmp_461_, v_x_463_, v_key_469_);
v___x_476_ = lean_unbox(v___x_475_);
switch(v___x_476_)
{
case 0:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_461_, v_lchild_468_, v_x_463_, v_x_464_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_477_);
v___x_479_ = v___x_473_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_key_469_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_val_470_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_rchild_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_480_, sizeof(void*)*4, v_color_467_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
case 1:
{
lean_object* v___x_482_; 
lean_dec(v_val_470_);
lean_dec(v_key_469_);
lean_dec_ref(v_cmp_461_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 2, v_x_464_);
lean_ctor_set(v___x_473_, 1, v_x_463_);
v___x_482_ = v___x_473_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_lchild_468_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_x_463_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v_x_464_);
lean_ctor_set(v_reuseFailAlloc_483_, 3, v_rchild_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_483_, sizeof(void*)*4, v_color_467_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
default: 
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_461_, v_rchild_471_, v_x_463_, v_x_464_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 3, v___x_484_);
v___x_486_ = v___x_473_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_lchild_468_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_key_469_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v_val_470_);
lean_ctor_set(v_reuseFailAlloc_487_, 3, v___x_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_487_, sizeof(void*)*4, v_color_467_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
else
{
lean_object* v_lchild_489_; lean_object* v_key_490_; lean_object* v_val_491_; lean_object* v_rchild_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_651_; 
v_lchild_489_ = lean_ctor_get(v_x_462_, 0);
v_key_490_ = lean_ctor_get(v_x_462_, 1);
v_val_491_ = lean_ctor_get(v_x_462_, 2);
v_rchild_492_ = lean_ctor_get(v_x_462_, 3);
v_isSharedCheck_651_ = !lean_is_exclusive(v_x_462_);
if (v_isSharedCheck_651_ == 0)
{
v___x_494_ = v_x_462_;
v_isShared_495_ = v_isSharedCheck_651_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_rchild_492_);
lean_inc(v_val_491_);
lean_inc(v_key_490_);
lean_inc(v_lchild_489_);
lean_dec(v_x_462_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_651_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; uint8_t v___x_497_; 
lean_inc_ref(v_cmp_461_);
lean_inc(v_key_490_);
lean_inc(v_x_463_);
v___x_496_ = lean_apply_2(v_cmp_461_, v_x_463_, v_key_490_);
v___x_497_ = lean_unbox(v___x_496_);
switch(v___x_497_)
{
case 0:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_461_, v_lchild_489_, v_x_463_, v_x_464_);
if (lean_obj_tag(v___x_498_) == 1)
{
uint8_t v_color_499_; lean_object* v_lchild_500_; lean_object* v_key_501_; lean_object* v_val_502_; lean_object* v_rchild_503_; lean_object* v_a_505_; lean_object* v_kx_506_; lean_object* v_vx_507_; lean_object* v_b_508_; lean_object* v_ky_509_; lean_object* v_vy_510_; lean_object* v_c_511_; lean_object* v_kz_512_; lean_object* v_vz_513_; lean_object* v_d_514_; 
v_color_499_ = lean_ctor_get_uint8(v___x_498_, sizeof(void*)*4);
v_lchild_500_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_lchild_500_);
v_key_501_ = lean_ctor_get(v___x_498_, 1);
v_val_502_ = lean_ctor_get(v___x_498_, 2);
v_rchild_503_ = lean_ctor_get(v___x_498_, 3);
lean_inc(v_rchild_503_);
if (v_color_499_ == 0)
{
if (lean_obj_tag(v_lchild_500_) == 1)
{
uint8_t v_color_520_; 
v_color_520_ = lean_ctor_get_uint8(v_lchild_500_, sizeof(void*)*4);
if (v_color_520_ == 0)
{
lean_object* v_lchild_521_; lean_object* v_key_522_; lean_object* v_val_523_; lean_object* v_rchild_524_; 
lean_inc(v_val_502_);
lean_inc(v_key_501_);
lean_dec_ref_known(v___x_498_, 4);
v_lchild_521_ = lean_ctor_get(v_lchild_500_, 0);
lean_inc(v_lchild_521_);
v_key_522_ = lean_ctor_get(v_lchild_500_, 1);
lean_inc(v_key_522_);
v_val_523_ = lean_ctor_get(v_lchild_500_, 2);
lean_inc(v_val_523_);
v_rchild_524_ = lean_ctor_get(v_lchild_500_, 3);
lean_inc(v_rchild_524_);
lean_dec_ref_known(v_lchild_500_, 4);
v_a_505_ = v_lchild_521_;
v_kx_506_ = v_key_522_;
v_vx_507_ = v_val_523_;
v_b_508_ = v_rchild_524_;
v_ky_509_ = v_key_501_;
v_vy_510_ = v_val_502_;
v_c_511_ = v_rchild_503_;
v_kz_512_ = v_key_490_;
v_vz_513_ = v_val_491_;
v_d_514_ = v_rchild_492_;
goto v___jp_504_;
}
else
{
if (lean_obj_tag(v_rchild_503_) == 1)
{
uint8_t v_color_525_; 
v_color_525_ = lean_ctor_get_uint8(v_rchild_503_, sizeof(void*)*4);
if (v_color_525_ == 0)
{
lean_object* v_lchild_526_; lean_object* v_key_527_; lean_object* v_val_528_; lean_object* v_rchild_529_; 
lean_inc(v_val_502_);
lean_inc(v_key_501_);
lean_dec_ref_known(v___x_498_, 4);
v_lchild_526_ = lean_ctor_get(v_rchild_503_, 0);
lean_inc(v_lchild_526_);
v_key_527_ = lean_ctor_get(v_rchild_503_, 1);
lean_inc(v_key_527_);
v_val_528_ = lean_ctor_get(v_rchild_503_, 2);
lean_inc(v_val_528_);
v_rchild_529_ = lean_ctor_get(v_rchild_503_, 3);
lean_inc(v_rchild_529_);
lean_dec_ref_known(v_rchild_503_, 4);
v_a_505_ = v_lchild_500_;
v_kx_506_ = v_key_501_;
v_vx_507_ = v_val_502_;
v_b_508_ = v_lchild_526_;
v_ky_509_ = v_key_527_;
v_vy_510_ = v_val_528_;
v_c_511_ = v_rchild_529_;
v_kz_512_ = v_key_490_;
v_vz_513_ = v_val_491_;
v_d_514_ = v_rchild_492_;
goto v___jp_504_;
}
else
{
lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref_known(v_lchild_500_, 4);
lean_del_object(v___x_494_);
v_isSharedCheck_536_ = !lean_is_exclusive(v_rchild_503_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; 
v_unused_537_ = lean_ctor_get(v_rchild_503_, 3);
lean_dec(v_unused_537_);
v_unused_538_ = lean_ctor_get(v_rchild_503_, 2);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_rchild_503_, 1);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_rchild_503_, 0);
lean_dec(v_unused_540_);
v___x_531_ = v_rchild_503_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_dec(v_rchild_503_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 3, v_rchild_492_);
lean_ctor_set(v___x_531_, 2, v_val_491_);
lean_ctor_set(v___x_531_, 1, v_key_490_);
lean_ctor_set(v___x_531_, 0, v___x_498_);
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_key_490_);
lean_ctor_set(v_reuseFailAlloc_535_, 2, v_val_491_);
lean_ctor_set(v_reuseFailAlloc_535_, 3, v_rchild_492_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*4, v_color_467_);
return v___x_534_;
}
}
}
}
else
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_rchild_503_);
lean_del_object(v___x_494_);
v_isSharedCheck_547_ = !lean_is_exclusive(v_lchild_500_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; lean_object* v_unused_549_; lean_object* v_unused_550_; lean_object* v_unused_551_; 
v_unused_548_ = lean_ctor_get(v_lchild_500_, 3);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_lchild_500_, 2);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_lchild_500_, 1);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_lchild_500_, 0);
lean_dec(v_unused_551_);
v___x_542_ = v_lchild_500_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_lchild_500_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 3, v_rchild_492_);
lean_ctor_set(v___x_542_, 2, v_val_491_);
lean_ctor_set(v___x_542_, 1, v_key_490_);
lean_ctor_set(v___x_542_, 0, v___x_498_);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_key_490_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_val_491_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_rchild_492_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*4, v_color_467_);
return v___x_545_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_503_) == 1)
{
uint8_t v_color_552_; 
v_color_552_ = lean_ctor_get_uint8(v_rchild_503_, sizeof(void*)*4);
if (v_color_552_ == 0)
{
lean_object* v_lchild_553_; lean_object* v_key_554_; lean_object* v_val_555_; lean_object* v_rchild_556_; 
lean_inc(v_val_502_);
lean_inc(v_key_501_);
lean_dec_ref_known(v___x_498_, 4);
v_lchild_553_ = lean_ctor_get(v_rchild_503_, 0);
lean_inc(v_lchild_553_);
v_key_554_ = lean_ctor_get(v_rchild_503_, 1);
lean_inc(v_key_554_);
v_val_555_ = lean_ctor_get(v_rchild_503_, 2);
lean_inc(v_val_555_);
v_rchild_556_ = lean_ctor_get(v_rchild_503_, 3);
lean_inc(v_rchild_556_);
lean_dec_ref_known(v_rchild_503_, 4);
v_a_505_ = v_lchild_500_;
v_kx_506_ = v_key_501_;
v_vx_507_ = v_val_502_;
v_b_508_ = v_lchild_553_;
v_ky_509_ = v_key_554_;
v_vy_510_ = v_val_555_;
v_c_511_ = v_rchild_556_;
v_kz_512_ = v_key_490_;
v_vz_513_ = v_val_491_;
v_d_514_ = v_rchild_492_;
goto v___jp_504_;
}
else
{
lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_lchild_500_);
lean_del_object(v___x_494_);
v_isSharedCheck_563_ = !lean_is_exclusive(v_rchild_503_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; 
v_unused_564_ = lean_ctor_get(v_rchild_503_, 3);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_rchild_503_, 2);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_rchild_503_, 1);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_rchild_503_, 0);
lean_dec(v_unused_567_);
v___x_558_ = v_rchild_503_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_dec(v_rchild_503_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 3, v_rchild_492_);
lean_ctor_set(v___x_558_, 2, v_val_491_);
lean_ctor_set(v___x_558_, 1, v_key_490_);
lean_ctor_set(v___x_558_, 0, v___x_498_);
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_key_490_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_val_491_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_rchild_492_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*4, v_color_467_);
return v___x_561_;
}
}
}
}
else
{
lean_object* v___x_568_; 
lean_dec(v_rchild_503_);
lean_dec(v_lchild_500_);
lean_del_object(v___x_494_);
v___x_568_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_568_, 0, v___x_498_);
lean_ctor_set(v___x_568_, 1, v_key_490_);
lean_ctor_set(v___x_568_, 2, v_val_491_);
lean_ctor_set(v___x_568_, 3, v_rchild_492_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*4, v_color_467_);
return v___x_568_;
}
}
}
else
{
lean_object* v___x_569_; 
lean_dec(v_rchild_503_);
lean_dec(v_lchild_500_);
lean_del_object(v___x_494_);
v___x_569_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_569_, 0, v___x_498_);
lean_ctor_set(v___x_569_, 1, v_key_490_);
lean_ctor_set(v___x_569_, 2, v_val_491_);
lean_ctor_set(v___x_569_, 3, v_rchild_492_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*4, v_color_467_);
return v___x_569_;
}
v___jp_504_:
{
lean_object* v___x_516_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 3, v_b_508_);
lean_ctor_set(v___x_494_, 2, v_vx_507_);
lean_ctor_set(v___x_494_, 1, v_kx_506_);
lean_ctor_set(v___x_494_, 0, v_a_505_);
v___x_516_ = v___x_494_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_505_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_kx_506_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_vx_507_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_b_508_);
lean_ctor_set_uint8(v_reuseFailAlloc_519_, sizeof(void*)*4, v_color_467_);
v___x_516_ = v_reuseFailAlloc_519_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_517_, 0, v_c_511_);
lean_ctor_set(v___x_517_, 1, v_kz_512_);
lean_ctor_set(v___x_517_, 2, v_vz_513_);
lean_ctor_set(v___x_517_, 3, v_d_514_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*4, v_color_467_);
v___x_518_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v_ky_509_);
lean_ctor_set(v___x_518_, 2, v_vy_510_);
lean_ctor_set(v___x_518_, 3, v___x_517_);
lean_ctor_set_uint8(v___x_518_, sizeof(void*)*4, v_color_499_);
return v___x_518_;
}
}
}
else
{
lean_object* v___x_571_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_498_);
v___x_571_ = v___x_494_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_key_490_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_val_491_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_rchild_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*4, v_color_467_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
case 1:
{
lean_object* v___x_574_; 
lean_dec(v_val_491_);
lean_dec(v_key_490_);
lean_dec_ref(v_cmp_461_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 2, v_x_464_);
lean_ctor_set(v___x_494_, 1, v_x_463_);
v___x_574_ = v___x_494_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_lchild_489_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_x_463_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_x_464_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_rchild_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_575_, sizeof(void*)*4, v_color_467_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
default: 
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_461_, v_rchild_492_, v_x_463_, v_x_464_);
if (lean_obj_tag(v___x_576_) == 1)
{
uint8_t v_color_577_; lean_object* v_lchild_578_; lean_object* v_key_579_; lean_object* v_val_580_; lean_object* v_rchild_581_; lean_object* v_a_583_; lean_object* v_kx_584_; lean_object* v_vx_585_; lean_object* v_b_586_; lean_object* v_ky_587_; lean_object* v_vy_588_; lean_object* v_c_589_; lean_object* v_kz_590_; lean_object* v_vz_591_; lean_object* v_d_592_; 
v_color_577_ = lean_ctor_get_uint8(v___x_576_, sizeof(void*)*4);
v_lchild_578_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_lchild_578_);
v_key_579_ = lean_ctor_get(v___x_576_, 1);
v_val_580_ = lean_ctor_get(v___x_576_, 2);
v_rchild_581_ = lean_ctor_get(v___x_576_, 3);
lean_inc(v_rchild_581_);
if (v_color_577_ == 0)
{
if (lean_obj_tag(v_lchild_578_) == 1)
{
uint8_t v_color_598_; 
v_color_598_ = lean_ctor_get_uint8(v_lchild_578_, sizeof(void*)*4);
if (v_color_598_ == 0)
{
lean_object* v_lchild_599_; lean_object* v_key_600_; lean_object* v_val_601_; lean_object* v_rchild_602_; 
lean_inc(v_val_580_);
lean_inc(v_key_579_);
lean_dec_ref_known(v___x_576_, 4);
v_lchild_599_ = lean_ctor_get(v_lchild_578_, 0);
lean_inc(v_lchild_599_);
v_key_600_ = lean_ctor_get(v_lchild_578_, 1);
lean_inc(v_key_600_);
v_val_601_ = lean_ctor_get(v_lchild_578_, 2);
lean_inc(v_val_601_);
v_rchild_602_ = lean_ctor_get(v_lchild_578_, 3);
lean_inc(v_rchild_602_);
lean_dec_ref_known(v_lchild_578_, 4);
v_a_583_ = v_lchild_489_;
v_kx_584_ = v_key_490_;
v_vx_585_ = v_val_491_;
v_b_586_ = v_lchild_599_;
v_ky_587_ = v_key_600_;
v_vy_588_ = v_val_601_;
v_c_589_ = v_rchild_602_;
v_kz_590_ = v_key_579_;
v_vz_591_ = v_val_580_;
v_d_592_ = v_rchild_581_;
goto v___jp_582_;
}
else
{
if (lean_obj_tag(v_rchild_581_) == 1)
{
uint8_t v_color_603_; 
v_color_603_ = lean_ctor_get_uint8(v_rchild_581_, sizeof(void*)*4);
if (v_color_603_ == 0)
{
lean_object* v_lchild_604_; lean_object* v_key_605_; lean_object* v_val_606_; lean_object* v_rchild_607_; 
lean_inc(v_val_580_);
lean_inc(v_key_579_);
lean_dec_ref_known(v___x_576_, 4);
v_lchild_604_ = lean_ctor_get(v_rchild_581_, 0);
lean_inc(v_lchild_604_);
v_key_605_ = lean_ctor_get(v_rchild_581_, 1);
lean_inc(v_key_605_);
v_val_606_ = lean_ctor_get(v_rchild_581_, 2);
lean_inc(v_val_606_);
v_rchild_607_ = lean_ctor_get(v_rchild_581_, 3);
lean_inc(v_rchild_607_);
lean_dec_ref_known(v_rchild_581_, 4);
v_a_583_ = v_lchild_489_;
v_kx_584_ = v_key_490_;
v_vx_585_ = v_val_491_;
v_b_586_ = v_lchild_578_;
v_ky_587_ = v_key_579_;
v_vy_588_ = v_val_580_;
v_c_589_ = v_lchild_604_;
v_kz_590_ = v_key_605_;
v_vz_591_ = v_val_606_;
v_d_592_ = v_rchild_607_;
goto v___jp_582_;
}
else
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref_known(v_lchild_578_, 4);
lean_del_object(v___x_494_);
v_isSharedCheck_614_ = !lean_is_exclusive(v_rchild_581_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; lean_object* v_unused_616_; lean_object* v_unused_617_; lean_object* v_unused_618_; 
v_unused_615_ = lean_ctor_get(v_rchild_581_, 3);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_rchild_581_, 2);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_rchild_581_, 1);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_rchild_581_, 0);
lean_dec(v_unused_618_);
v___x_609_ = v_rchild_581_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_dec(v_rchild_581_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 3, v___x_576_);
lean_ctor_set(v___x_609_, 2, v_val_491_);
lean_ctor_set(v___x_609_, 1, v_key_490_);
lean_ctor_set(v___x_609_, 0, v_lchild_489_);
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_lchild_489_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_key_490_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_val_491_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v___x_576_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*4, v_color_467_);
return v___x_612_;
}
}
}
}
else
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_rchild_581_);
lean_del_object(v___x_494_);
v_isSharedCheck_625_ = !lean_is_exclusive(v_lchild_578_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; lean_object* v_unused_627_; lean_object* v_unused_628_; lean_object* v_unused_629_; 
v_unused_626_ = lean_ctor_get(v_lchild_578_, 3);
lean_dec(v_unused_626_);
v_unused_627_ = lean_ctor_get(v_lchild_578_, 2);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_lchild_578_, 1);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_lchild_578_, 0);
lean_dec(v_unused_629_);
v___x_620_ = v_lchild_578_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_dec(v_lchild_578_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 3, v___x_576_);
lean_ctor_set(v___x_620_, 2, v_val_491_);
lean_ctor_set(v___x_620_, 1, v_key_490_);
lean_ctor_set(v___x_620_, 0, v_lchild_489_);
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_lchild_489_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_key_490_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_val_491_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v___x_576_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*4, v_color_467_);
return v___x_623_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_rchild_581_) == 1)
{
uint8_t v_color_630_; 
v_color_630_ = lean_ctor_get_uint8(v_rchild_581_, sizeof(void*)*4);
if (v_color_630_ == 0)
{
lean_object* v_lchild_631_; lean_object* v_key_632_; lean_object* v_val_633_; lean_object* v_rchild_634_; 
lean_inc(v_val_580_);
lean_inc(v_key_579_);
lean_dec_ref_known(v___x_576_, 4);
v_lchild_631_ = lean_ctor_get(v_rchild_581_, 0);
lean_inc(v_lchild_631_);
v_key_632_ = lean_ctor_get(v_rchild_581_, 1);
lean_inc(v_key_632_);
v_val_633_ = lean_ctor_get(v_rchild_581_, 2);
lean_inc(v_val_633_);
v_rchild_634_ = lean_ctor_get(v_rchild_581_, 3);
lean_inc(v_rchild_634_);
lean_dec_ref_known(v_rchild_581_, 4);
v_a_583_ = v_lchild_489_;
v_kx_584_ = v_key_490_;
v_vx_585_ = v_val_491_;
v_b_586_ = v_lchild_578_;
v_ky_587_ = v_key_579_;
v_vy_588_ = v_val_580_;
v_c_589_ = v_lchild_631_;
v_kz_590_ = v_key_632_;
v_vz_591_ = v_val_633_;
v_d_592_ = v_rchild_634_;
goto v___jp_582_;
}
else
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v_lchild_578_);
lean_del_object(v___x_494_);
v_isSharedCheck_641_ = !lean_is_exclusive(v_rchild_581_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; lean_object* v_unused_643_; lean_object* v_unused_644_; lean_object* v_unused_645_; 
v_unused_642_ = lean_ctor_get(v_rchild_581_, 3);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v_rchild_581_, 2);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_rchild_581_, 1);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_rchild_581_, 0);
lean_dec(v_unused_645_);
v___x_636_ = v_rchild_581_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_dec(v_rchild_581_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 3, v___x_576_);
lean_ctor_set(v___x_636_, 2, v_val_491_);
lean_ctor_set(v___x_636_, 1, v_key_490_);
lean_ctor_set(v___x_636_, 0, v_lchild_489_);
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_lchild_489_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_key_490_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_val_491_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v___x_576_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_ctor_set_uint8(v___x_639_, sizeof(void*)*4, v_color_467_);
return v___x_639_;
}
}
}
}
else
{
lean_object* v___x_646_; 
lean_dec(v_rchild_581_);
lean_dec(v_lchild_578_);
lean_del_object(v___x_494_);
v___x_646_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_646_, 0, v_lchild_489_);
lean_ctor_set(v___x_646_, 1, v_key_490_);
lean_ctor_set(v___x_646_, 2, v_val_491_);
lean_ctor_set(v___x_646_, 3, v___x_576_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*4, v_color_467_);
return v___x_646_;
}
}
}
else
{
lean_object* v___x_647_; 
lean_dec(v_rchild_581_);
lean_dec(v_lchild_578_);
lean_del_object(v___x_494_);
v___x_647_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_647_, 0, v_lchild_489_);
lean_ctor_set(v___x_647_, 1, v_key_490_);
lean_ctor_set(v___x_647_, 2, v_val_491_);
lean_ctor_set(v___x_647_, 3, v___x_576_);
lean_ctor_set_uint8(v___x_647_, sizeof(void*)*4, v_color_467_);
return v___x_647_;
}
v___jp_582_:
{
lean_object* v___x_594_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 3, v_b_586_);
lean_ctor_set(v___x_494_, 2, v_vx_585_);
lean_ctor_set(v___x_494_, 1, v_kx_584_);
lean_ctor_set(v___x_494_, 0, v_a_583_);
v___x_594_ = v___x_494_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_583_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_kx_584_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_vx_585_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_b_586_);
lean_ctor_set_uint8(v_reuseFailAlloc_597_, sizeof(void*)*4, v_color_467_);
v___x_594_ = v_reuseFailAlloc_597_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_595_, 0, v_c_589_);
lean_ctor_set(v___x_595_, 1, v_kz_590_);
lean_ctor_set(v___x_595_, 2, v_vz_591_);
lean_ctor_set(v___x_595_, 3, v_d_592_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*4, v_color_467_);
v___x_596_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v_ky_587_);
lean_ctor_set(v___x_596_, 2, v_vy_588_);
lean_ctor_set(v___x_596_, 3, v___x_595_);
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*4, v_color_577_);
return v___x_596_;
}
}
}
else
{
lean_object* v___x_649_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 3, v___x_576_);
v___x_649_ = v___x_494_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_lchild_489_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_key_490_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_val_491_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v___x_576_);
lean_ctor_set_uint8(v_reuseFailAlloc_650_, sizeof(void*)*4, v_color_467_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(lean_object* v_cmp_652_, lean_object* v_t_653_, lean_object* v_k_654_, lean_object* v_v_655_){
_start:
{
uint8_t v___x_656_; 
v___x_656_ = l_Lean_RBNode_isRed___redArg(v_t_653_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_652_, v_t_653_, v_k_654_, v_v_655_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_652_, v_t_653_, v_k_654_, v_v_655_);
v___x_659_ = l_Lean_RBNode_setBlack___redArg(v___x_658_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(lean_object* v_cmp_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
lean_dec_ref(v_cmp_660_);
return v_x_661_;
}
else
{
lean_object* v_head_663_; lean_object* v_tail_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_head_663_ = lean_ctor_get(v_x_662_, 0);
lean_inc(v_head_663_);
v_tail_664_ = lean_ctor_get(v_x_662_, 1);
lean_inc(v_tail_664_);
lean_dec_ref_known(v_x_662_, 2);
v___x_665_ = lean_box(0);
lean_inc_ref(v_cmp_660_);
v___x_666_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_660_, v_x_661_, v_head_663_, v___x_665_);
v_x_661_ = v___x_666_;
v_x_662_ = v_tail_664_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList___redArg(lean_object* v_l_668_, lean_object* v_cmp_669_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box(0);
v___x_671_ = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(v_cmp_669_, v___x_670_, v_l_668_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromList(lean_object* v_00_u03b1_672_, lean_object* v_l_673_, lean_object* v_cmp_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_RBTree_fromList___redArg(v_l_673_, v_cmp_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0(lean_object* v_00_u03b1_676_, lean_object* v_cmp_677_, lean_object* v_00_u03b2_678_, lean_object* v_t_679_, lean_object* v_k_680_, lean_object* v_v_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_677_, v_t_679_, v_k_680_, v_v_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_RBTree_fromList_spec__1(lean_object* v_00_u03b1_683_, lean_object* v_cmp_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_List_foldl___at___00Lean_RBTree_fromList_spec__1___redArg(v_cmp_684_, v_x_685_, v_x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0(lean_object* v_00_u03b1_688_, lean_object* v_cmp_689_, lean_object* v_00_u03b2_690_, lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_RBNode_ins___at___00Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0_spec__0___redArg(v_cmp_689_, v_x_691_, v_x_692_, v_x_693_);
return v___x_694_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(lean_object* v_cmp_695_, lean_object* v_as_696_, size_t v_i_697_, size_t v_stop_698_, lean_object* v_b_699_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = lean_usize_dec_eq(v_i_697_, v_stop_698_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; size_t v___x_704_; size_t v___x_705_; 
v___x_701_ = lean_array_uget_borrowed(v_as_696_, v_i_697_);
v___x_702_ = lean_box(0);
lean_inc(v___x_701_);
lean_inc_ref(v_cmp_695_);
v___x_703_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_695_, v_b_699_, v___x_701_, v___x_702_);
v___x_704_ = ((size_t)1ULL);
v___x_705_ = lean_usize_add(v_i_697_, v___x_704_);
v_i_697_ = v___x_705_;
v_b_699_ = v___x_703_;
goto _start;
}
else
{
lean_dec_ref(v_cmp_695_);
return v_b_699_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_695_ = stack[0].m_obj;
lean_object* v_as_696_ = stack[1].m_obj;
size_t v_i_697_ = stack[2].m_num;
size_t v_stop_698_ = stack[3].m_num;
lean_object* v_b_699_ = stack[4].m_obj;
lean_object* v_res_707_;
v_res_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_695_, v_as_696_, v_i_697_, v_stop_698_, v_b_699_);
stack->m_obj
 = v_res_707_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg___boxed(lean_object* v_cmp_708_, lean_object* v_as_709_, lean_object* v_i_710_, lean_object* v_stop_711_, lean_object* v_b_712_){
_start:
{
size_t v_i_boxed_713_; size_t v_stop_boxed_714_; lean_object* v_res_715_; 
v_i_boxed_713_ = lean_unbox_usize(v_i_710_);
lean_dec(v_i_710_);
v_stop_boxed_714_ = lean_unbox_usize(v_stop_711_);
lean_dec(v_stop_711_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_708_, v_as_709_, v_i_boxed_713_, v_stop_boxed_714_, v_b_712_);
lean_dec_ref(v_as_709_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg(lean_object* v_l_716_, lean_object* v_cmp_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_718_ = lean_box(0);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_array_get_size(v_l_716_);
v___x_721_ = lean_nat_dec_lt(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
lean_dec_ref(v_cmp_717_);
return v___x_718_;
}
else
{
uint8_t v___x_722_; 
v___x_722_ = lean_nat_dec_le(v___x_720_, v___x_720_);
if (v___x_722_ == 0)
{
if (v___x_721_ == 0)
{
lean_dec_ref(v_cmp_717_);
return v___x_718_;
}
else
{
size_t v___x_723_; size_t v___x_724_; lean_object* v___x_725_; 
v___x_723_ = ((size_t)0ULL);
v___x_724_ = lean_usize_of_nat(v___x_720_);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_717_, v_l_716_, v___x_723_, v___x_724_, v___x_718_);
return v___x_725_;
}
}
else
{
size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; 
v___x_726_ = ((size_t)0ULL);
v___x_727_ = lean_usize_of_nat(v___x_720_);
v___x_728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_717_, v_l_716_, v___x_726_, v___x_727_, v___x_718_);
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___redArg___boxed(lean_object* v_l_729_, lean_object* v_cmp_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_RBTree_fromArray___redArg(v_l_729_, v_cmp_730_);
lean_dec_ref(v_l_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray(lean_object* v_00_u03b1_732_, lean_object* v_l_733_, lean_object* v_cmp_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_RBTree_fromArray___redArg(v_l_733_, v_cmp_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_fromArray___boxed(lean_object* v_00_u03b1_736_, lean_object* v_l_737_, lean_object* v_cmp_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_RBTree_fromArray(v_00_u03b1_736_, v_l_737_, v_cmp_738_);
lean_dec_ref(v_l_737_);
return v_res_739_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(lean_object* v_00_u03b1_740_, lean_object* v_cmp_741_, lean_object* v_as_742_, size_t v_i_743_, size_t v_stop_744_, lean_object* v_b_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___redArg(v_cmp_741_, v_as_742_, v_i_743_, v_stop_744_, v_b_745_);
return v___x_746_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_741_ = stack[1].m_obj;
lean_object* v_as_742_ = stack[2].m_obj;
size_t v_i_743_ = stack[3].m_num;
size_t v_stop_744_ = stack[4].m_num;
lean_object* v_b_745_ = stack[5].m_obj;
lean_object* v_res_747_;
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(lean_box(0), v_cmp_741_, v_as_742_, v_i_743_, v_stop_744_, v_b_745_);
stack->m_obj
 = v_res_747_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0___boxed(lean_object* v_00_u03b1_748_, lean_object* v_cmp_749_, lean_object* v_as_750_, lean_object* v_i_751_, lean_object* v_stop_752_, lean_object* v_b_753_){
_start:
{
size_t v_i_boxed_754_; size_t v_stop_boxed_755_; lean_object* v_res_756_; 
v_i_boxed_754_ = lean_unbox_usize(v_i_751_);
lean_dec(v_i_751_);
v_stop_boxed_755_ = lean_unbox_usize(v_stop_752_);
lean_dec(v_stop_752_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_RBTree_fromArray_spec__0(v_00_u03b1_748_, v_cmp_749_, v_as_750_, v_i_boxed_754_, v_stop_boxed_755_, v_b_753_);
lean_dec_ref(v_as_750_);
return v_res_756_;
}
}
uint8_t l_Lean_RBTree_all___redArg___lam__0(lean_object* v_p_757_, lean_object* v_a_758_, lean_object* v_x_759_){
_start:
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_apply_1(v_p_757_, v_a_758_);
v___x_761_ = lean_unbox(v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT void l_Lean_RBTree_all___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_757_ = stack[0].m_obj;
lean_object* v_a_758_ = stack[1].m_obj;
lean_object* v_x_759_ = stack[2].m_obj;
uint8_t v_res_762_;
v_res_762_ = l_Lean_RBTree_all___redArg___lam__0(v_p_757_, v_a_758_, v_x_759_);
stack->m_num = v_res_762_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___lam__0___boxed(lean_object* v_p_763_, lean_object* v_a_764_, lean_object* v_x_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_Lean_RBTree_all___redArg___lam__0(v_p_763_, v_a_764_, v_x_765_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
uint8_t l_Lean_RBTree_all___redArg(lean_object* v_t_768_, lean_object* v_p_769_){
_start:
{
lean_object* v___f_770_; uint8_t v___x_771_; 
v___f_770_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_770_, 0, v_p_769_);
v___x_771_ = l_Lean_RBNode_all___redArg(v___f_770_, v_t_768_);
return v___x_771_;
}
}
LEAN_EXPORT void l_Lean_RBTree_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_768_ = stack[0].m_obj;
lean_object* v_p_769_ = stack[1].m_obj;
uint8_t v_res_772_;
v_res_772_ = l_Lean_RBTree_all___redArg(v_t_768_, v_p_769_);
stack->m_num = v_res_772_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___redArg___boxed(lean_object* v_t_773_, lean_object* v_p_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l_Lean_RBTree_all___redArg(v_t_773_, v_p_774_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
uint8_t l_Lean_RBTree_all(lean_object* v_00_u03b1_777_, lean_object* v_cmp_778_, lean_object* v_t_779_, lean_object* v_p_780_){
_start:
{
lean_object* v___f_781_; uint8_t v___x_782_; 
v___f_781_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_781_, 0, v_p_780_);
v___x_782_ = l_Lean_RBNode_all___redArg(v___f_781_, v_t_779_);
return v___x_782_;
}
}
LEAN_EXPORT void l_Lean_RBTree_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_778_ = stack[1].m_obj;
lean_object* v_t_779_ = stack[2].m_obj;
lean_object* v_p_780_ = stack[3].m_obj;
uint8_t v_res_783_;
v_res_783_ = l_Lean_RBTree_all(lean_box(0), v_cmp_778_, v_t_779_, v_p_780_);
stack->m_num = v_res_783_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_all___boxed(lean_object* v_00_u03b1_784_, lean_object* v_cmp_785_, lean_object* v_t_786_, lean_object* v_p_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l_Lean_RBTree_all(v_00_u03b1_784_, v_cmp_785_, v_t_786_, v_p_787_);
lean_dec_ref(v_cmp_785_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
uint8_t l_Lean_RBTree_any___redArg(lean_object* v_t_790_, lean_object* v_p_791_){
_start:
{
lean_object* v___f_792_; uint8_t v___x_793_; 
v___f_792_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_792_, 0, v_p_791_);
v___x_793_ = l_Lean_RBNode_any___redArg(v___f_792_, v_t_790_);
return v___x_793_;
}
}
LEAN_EXPORT void l_Lean_RBTree_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_790_ = stack[0].m_obj;
lean_object* v_p_791_ = stack[1].m_obj;
uint8_t v_res_794_;
v_res_794_ = l_Lean_RBTree_any___redArg(v_t_790_, v_p_791_);
stack->m_num = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_any___redArg___boxed(lean_object* v_t_795_, lean_object* v_p_796_){
_start:
{
uint8_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l_Lean_RBTree_any___redArg(v_t_795_, v_p_796_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
uint8_t l_Lean_RBTree_any(lean_object* v_00_u03b1_799_, lean_object* v_cmp_800_, lean_object* v_t_801_, lean_object* v_p_802_){
_start:
{
lean_object* v___f_803_; uint8_t v___x_804_; 
v___f_803_ = lean_alloc_closure((void*)(l_Lean_RBTree_all___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_803_, 0, v_p_802_);
v___x_804_ = l_Lean_RBNode_any___redArg(v___f_803_, v_t_801_);
return v___x_804_;
}
}
LEAN_EXPORT void l_Lean_RBTree_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_800_ = stack[1].m_obj;
lean_object* v_t_801_ = stack[2].m_obj;
lean_object* v_p_802_ = stack[3].m_obj;
uint8_t v_res_805_;
v_res_805_ = l_Lean_RBTree_any(lean_box(0), v_cmp_800_, v_t_801_, v_p_802_);
stack->m_num = v_res_805_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_any___boxed(lean_object* v_00_u03b1_806_, lean_object* v_cmp_807_, lean_object* v_t_808_, lean_object* v_p_809_){
_start:
{
uint8_t v_res_810_; lean_object* v_r_811_; 
v_res_810_ = l_Lean_RBTree_any(v_00_u03b1_806_, v_cmp_807_, v_t_808_, v_p_809_);
lean_dec_ref(v_cmp_807_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(lean_object* v_cmp_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
if (lean_obj_tag(v_x_813_) == 0)
{
lean_object* v___x_815_; 
lean_dec(v_x_814_);
lean_dec_ref(v_cmp_812_);
v___x_815_ = lean_box(0);
return v___x_815_;
}
else
{
lean_object* v_lchild_816_; lean_object* v_key_817_; lean_object* v_val_818_; lean_object* v_rchild_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_lchild_816_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_lchild_816_);
v_key_817_ = lean_ctor_get(v_x_813_, 1);
lean_inc_n(v_key_817_, 2);
v_val_818_ = lean_ctor_get(v_x_813_, 2);
lean_inc(v_val_818_);
v_rchild_819_ = lean_ctor_get(v_x_813_, 3);
lean_inc(v_rchild_819_);
lean_dec_ref_known(v_x_813_, 4);
lean_inc_ref(v_cmp_812_);
lean_inc(v_x_814_);
v___x_820_ = lean_apply_2(v_cmp_812_, v_x_814_, v_key_817_);
v___x_821_ = lean_unbox(v___x_820_);
switch(v___x_821_)
{
case 0:
{
lean_dec(v_rchild_819_);
lean_dec(v_val_818_);
lean_dec(v_key_817_);
v_x_813_ = v_lchild_816_;
goto _start;
}
case 1:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec(v_rchild_819_);
lean_dec(v_lchild_816_);
lean_dec(v_x_814_);
lean_dec_ref(v_cmp_812_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v_key_817_);
lean_ctor_set(v___x_823_, 1, v_val_818_);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
default: 
{
lean_dec(v_val_818_);
lean_dec(v_key_817_);
lean_dec(v_lchild_816_);
v_x_813_ = v_rchild_819_;
goto _start;
}
}
}
}
}
uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(lean_object* v_t_u2082_826_, lean_object* v_cmp_827_, lean_object* v_x_828_){
_start:
{
if (lean_obj_tag(v_x_828_) == 0)
{
uint8_t v___x_829_; 
lean_dec_ref(v_cmp_827_);
lean_dec(v_t_u2082_826_);
v___x_829_ = 1;
return v___x_829_;
}
else
{
lean_object* v_lchild_830_; lean_object* v_key_831_; lean_object* v_rchild_832_; lean_object* v___x_833_; 
v_lchild_830_ = lean_ctor_get(v_x_828_, 0);
lean_inc(v_lchild_830_);
v_key_831_ = lean_ctor_get(v_x_828_, 1);
lean_inc(v_key_831_);
v_rchild_832_ = lean_ctor_get(v_x_828_, 3);
lean_inc(v_rchild_832_);
lean_dec_ref_known(v_x_828_, 4);
lean_inc(v_t_u2082_826_);
lean_inc_ref(v_cmp_827_);
v___x_833_ = l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(v_cmp_827_, v_t_u2082_826_, v_key_831_);
if (lean_obj_tag(v___x_833_) == 0)
{
uint8_t v___x_834_; 
lean_dec(v_rchild_832_);
lean_dec(v_lchild_830_);
lean_dec_ref(v_cmp_827_);
lean_dec(v_t_u2082_826_);
v___x_834_ = 0;
return v___x_834_;
}
else
{
uint8_t v___x_835_; 
lean_dec_ref_known(v___x_833_, 1);
lean_inc_ref(v_cmp_827_);
lean_inc(v_t_u2082_826_);
v___x_835_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_826_, v_cmp_827_, v_lchild_830_);
if (v___x_835_ == 0)
{
lean_dec(v_rchild_832_);
lean_dec_ref(v_cmp_827_);
lean_dec(v_t_u2082_826_);
return v___x_835_;
}
else
{
v_x_828_ = v_rchild_832_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_u2082_826_ = stack[0].m_obj;
lean_object* v_cmp_827_ = stack[1].m_obj;
lean_object* v_x_828_ = stack[2].m_obj;
uint8_t v_res_837_;
v_res_837_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_826_, v_cmp_827_, v_x_828_);
stack->m_num = v_res_837_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg___boxed(lean_object* v_t_u2082_838_, lean_object* v_cmp_839_, lean_object* v_x_840_){
_start:
{
uint8_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_838_, v_cmp_839_, v_x_840_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
uint8_t l_Lean_RBTree_subset___redArg(lean_object* v_cmp_843_, lean_object* v_t_u2081_844_, lean_object* v_t_u2082_845_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_845_, v_cmp_843_, v_t_u2081_844_);
return v___x_846_;
}
}
LEAN_EXPORT void l_Lean_RBTree_subset___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_843_ = stack[0].m_obj;
lean_object* v_t_u2081_844_ = stack[1].m_obj;
lean_object* v_t_u2082_845_ = stack[2].m_obj;
uint8_t v_res_847_;
v_res_847_ = l_Lean_RBTree_subset___redArg(v_cmp_843_, v_t_u2081_844_, v_t_u2082_845_);
stack->m_num = v_res_847_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___redArg___boxed(lean_object* v_cmp_848_, lean_object* v_t_u2081_849_, lean_object* v_t_u2082_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_Lean_RBTree_subset___redArg(v_cmp_848_, v_t_u2081_849_, v_t_u2082_850_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
uint8_t l_Lean_RBTree_subset(lean_object* v_00_u03b1_853_, lean_object* v_cmp_854_, lean_object* v_t_u2081_855_, lean_object* v_t_u2082_856_){
_start:
{
uint8_t v___x_857_; 
v___x_857_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_856_, v_cmp_854_, v_t_u2081_855_);
return v___x_857_;
}
}
LEAN_EXPORT void l_Lean_RBTree_subset_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_854_ = stack[1].m_obj;
lean_object* v_t_u2081_855_ = stack[2].m_obj;
lean_object* v_t_u2082_856_ = stack[3].m_obj;
uint8_t v_res_858_;
v_res_858_ = l_Lean_RBTree_subset(lean_box(0), v_cmp_854_, v_t_u2081_855_, v_t_u2082_856_);
stack->m_num = v_res_858_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_subset___boxed(lean_object* v_00_u03b1_859_, lean_object* v_cmp_860_, lean_object* v_t_u2081_861_, lean_object* v_t_u2082_862_){
_start:
{
uint8_t v_res_863_; lean_object* v_r_864_; 
v_res_863_ = l_Lean_RBTree_subset(v_00_u03b1_859_, v_cmp_860_, v_t_u2081_861_, v_t_u2082_862_);
v_r_864_ = lean_box(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0(lean_object* v_00_u03b1_865_, lean_object* v_cmp_866_, lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_RBNode_findCore___at___00Lean_RBTree_subset_spec__0___redArg(v_cmp_866_, v_x_868_, v_x_869_);
return v___x_870_;
}
}
uint8_t l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(lean_object* v_00_u03b1_871_, lean_object* v_t_u2082_872_, lean_object* v_cmp_873_, lean_object* v_x_874_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_872_, v_cmp_873_, v_x_874_);
return v___x_875_;
}
}
LEAN_EXPORT void l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_u2082_872_ = stack[1].m_obj;
lean_object* v_cmp_873_ = stack[2].m_obj;
lean_object* v_x_874_ = stack[3].m_obj;
uint8_t v_res_876_;
v_res_876_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(lean_box(0), v_t_u2082_872_, v_cmp_873_, v_x_874_);
stack->m_num = v_res_876_;
}
LEAN_EXPORT lean_object* l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___boxed(lean_object* v_00_u03b1_877_, lean_object* v_t_u2082_878_, lean_object* v_cmp_879_, lean_object* v_x_880_){
_start:
{
uint8_t v_res_881_; lean_object* v_r_882_; 
v_res_881_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1(v_00_u03b1_877_, v_t_u2082_878_, v_cmp_879_, v_x_880_);
v_r_882_ = lean_box(v_res_881_);
return v_r_882_;
}
}
uint8_t l_Lean_RBTree_seteq___redArg(lean_object* v_cmp_883_, lean_object* v_t_u2081_884_, lean_object* v_t_u2082_885_){
_start:
{
uint8_t v___x_886_; 
lean_inc(v_t_u2081_884_);
lean_inc_ref(v_cmp_883_);
lean_inc(v_t_u2082_885_);
v___x_886_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2082_885_, v_cmp_883_, v_t_u2081_884_);
if (v___x_886_ == 0)
{
lean_dec(v_t_u2082_885_);
lean_dec(v_t_u2081_884_);
lean_dec_ref(v_cmp_883_);
return v___x_886_;
}
else
{
uint8_t v___x_887_; 
v___x_887_ = l_Lean_RBNode_all___at___00Lean_RBTree_subset_spec__1___redArg(v_t_u2081_884_, v_cmp_883_, v_t_u2082_885_);
return v___x_887_;
}
}
}
LEAN_EXPORT void l_Lean_RBTree_seteq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_883_ = stack[0].m_obj;
lean_object* v_t_u2081_884_ = stack[1].m_obj;
lean_object* v_t_u2082_885_ = stack[2].m_obj;
uint8_t v_res_888_;
v_res_888_ = l_Lean_RBTree_seteq___redArg(v_cmp_883_, v_t_u2081_884_, v_t_u2082_885_);
stack->m_num = v_res_888_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___redArg___boxed(lean_object* v_cmp_889_, lean_object* v_t_u2081_890_, lean_object* v_t_u2082_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = l_Lean_RBTree_seteq___redArg(v_cmp_889_, v_t_u2081_890_, v_t_u2082_891_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
uint8_t l_Lean_RBTree_seteq(lean_object* v_00_u03b1_894_, lean_object* v_cmp_895_, lean_object* v_t_u2081_896_, lean_object* v_t_u2082_897_){
_start:
{
uint8_t v___x_898_; 
v___x_898_ = l_Lean_RBTree_seteq___redArg(v_cmp_895_, v_t_u2081_896_, v_t_u2082_897_);
return v___x_898_;
}
}
LEAN_EXPORT void l_Lean_RBTree_seteq_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_895_ = stack[1].m_obj;
lean_object* v_t_u2081_896_ = stack[2].m_obj;
lean_object* v_t_u2082_897_ = stack[3].m_obj;
uint8_t v_res_899_;
v_res_899_ = l_Lean_RBTree_seteq(lean_box(0), v_cmp_895_, v_t_u2081_896_, v_t_u2082_897_);
stack->m_num = v_res_899_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_seteq___boxed(lean_object* v_00_u03b1_900_, lean_object* v_cmp_901_, lean_object* v_t_u2081_902_, lean_object* v_t_u2082_903_){
_start:
{
uint8_t v_res_904_; lean_object* v_r_905_; 
v_res_904_ = l_Lean_RBTree_seteq(v_00_u03b1_900_, v_cmp_901_, v_t_u2081_902_, v_t_u2082_903_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(lean_object* v_cmp_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
if (lean_obj_tag(v_x_908_) == 0)
{
lean_dec_ref(v_cmp_906_);
return v_x_907_;
}
else
{
lean_object* v_lchild_909_; lean_object* v_key_910_; lean_object* v_rchild_911_; lean_object* v_val_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_lchild_909_ = lean_ctor_get(v_x_908_, 0);
lean_inc(v_lchild_909_);
v_key_910_ = lean_ctor_get(v_x_908_, 1);
lean_inc(v_key_910_);
v_rchild_911_ = lean_ctor_get(v_x_908_, 3);
lean_inc(v_rchild_911_);
lean_dec_ref_known(v_x_908_, 4);
lean_inc_ref_n(v_cmp_906_, 2);
v_val_912_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(v_cmp_906_, v_x_907_, v_lchild_909_);
v___x_913_ = lean_box(0);
v___x_914_ = l_Lean_RBNode_insert___at___00Lean_RBTree_fromList_spec__0___redArg(v_cmp_906_, v_val_912_, v_key_910_, v___x_913_);
v_x_907_ = v___x_914_;
v_x_908_ = v_rchild_911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_union___redArg(lean_object* v_cmp_916_, lean_object* v_t_u2081_917_, lean_object* v_t_u2082_918_){
_start:
{
if (lean_obj_tag(v_t_u2081_917_) == 0)
{
lean_dec_ref(v_cmp_916_);
return v_t_u2082_918_;
}
else
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(v_cmp_916_, v_t_u2081_917_, v_t_u2082_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_union(lean_object* v_00_u03b1_920_, lean_object* v_cmp_921_, lean_object* v_t_u2081_922_, lean_object* v_t_u2082_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_RBTree_union___redArg(v_cmp_921_, v_t_u2081_922_, v_t_u2082_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0(lean_object* v_00_u03b1_925_, lean_object* v_cmp_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_RBNode_fold___at___00Lean_RBTree_union_spec__0___redArg(v_cmp_926_, v_x_927_, v_x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(lean_object* v_cmp_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
if (lean_obj_tag(v_x_932_) == 0)
{
lean_dec(v_x_931_);
lean_dec_ref(v_cmp_930_);
return v_x_932_;
}
else
{
lean_object* v_lchild_933_; lean_object* v_key_934_; lean_object* v_val_935_; lean_object* v_rchild_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_959_; 
v_lchild_933_ = lean_ctor_get(v_x_932_, 0);
v_key_934_ = lean_ctor_get(v_x_932_, 1);
v_val_935_ = lean_ctor_get(v_x_932_, 2);
v_rchild_936_ = lean_ctor_get(v_x_932_, 3);
v_isSharedCheck_959_ = !lean_is_exclusive(v_x_932_);
if (v_isSharedCheck_959_ == 0)
{
v___x_938_ = v_x_932_;
v_isShared_939_ = v_isSharedCheck_959_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_rchild_936_);
lean_inc(v_val_935_);
lean_inc(v_key_934_);
lean_inc(v_lchild_933_);
lean_dec(v_x_932_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_959_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; uint8_t v___x_941_; 
lean_inc_ref(v_cmp_930_);
lean_inc(v_key_934_);
lean_inc(v_x_931_);
v___x_940_ = lean_apply_2(v_cmp_930_, v_x_931_, v_key_934_);
v___x_941_ = lean_unbox(v___x_940_);
switch(v___x_941_)
{
case 0:
{
uint8_t v___x_942_; 
v___x_942_ = l_Lean_RBNode_isBlack___redArg(v_lchild_933_);
if (v___x_942_ == 0)
{
uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = 0;
v___x_944_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_930_, v_x_931_, v_lchild_933_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_944_);
v___x_946_ = v___x_938_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_key_934_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_val_935_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_rchild_936_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_ctor_set_uint8(v___x_946_, sizeof(void*)*4, v___x_943_);
return v___x_946_;
}
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_del_object(v___x_938_);
v___x_948_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_930_, v_x_931_, v_lchild_933_);
v___x_949_ = l_Lean_RBNode_balLeft___redArg(v___x_948_, v_key_934_, v_val_935_, v_rchild_936_);
return v___x_949_;
}
}
case 1:
{
lean_object* v___x_950_; 
lean_del_object(v___x_938_);
lean_dec(v_val_935_);
lean_dec(v_key_934_);
lean_dec(v_x_931_);
lean_dec_ref(v_cmp_930_);
v___x_950_ = l_Lean_RBNode_appendTrees___redArg(v_lchild_933_, v_rchild_936_);
return v___x_950_;
}
default: 
{
uint8_t v___x_951_; 
v___x_951_ = l_Lean_RBNode_isBlack___redArg(v_rchild_936_);
if (v___x_951_ == 0)
{
uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_952_ = 0;
v___x_953_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_930_, v_x_931_, v_rchild_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 3, v___x_953_);
v___x_955_ = v___x_938_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_lchild_933_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_key_934_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_val_935_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_ctor_set_uint8(v___x_955_, sizeof(void*)*4, v___x_952_);
return v___x_955_;
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_del_object(v___x_938_);
v___x_957_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_930_, v_x_931_, v_rchild_936_);
v___x_958_ = l_Lean_RBNode_balRight___redArg(v_lchild_933_, v_key_934_, v_val_935_, v___x_957_);
return v___x_958_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(lean_object* v_cmp_960_, lean_object* v_x_961_, lean_object* v_t_962_){
_start:
{
lean_object* v_t_963_; lean_object* v___x_964_; 
v_t_963_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_960_, v_x_961_, v_t_962_);
v___x_964_ = l_Lean_RBNode_setBlack___redArg(v_t_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(lean_object* v_cmp_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
if (lean_obj_tag(v_x_967_) == 0)
{
lean_dec_ref(v_cmp_965_);
return v_x_966_;
}
else
{
lean_object* v_lchild_968_; lean_object* v_key_969_; lean_object* v_rchild_970_; lean_object* v_val_971_; lean_object* v___x_972_; 
v_lchild_968_ = lean_ctor_get(v_x_967_, 0);
lean_inc(v_lchild_968_);
v_key_969_ = lean_ctor_get(v_x_967_, 1);
lean_inc(v_key_969_);
v_rchild_970_ = lean_ctor_get(v_x_967_, 3);
lean_inc(v_rchild_970_);
lean_dec_ref_known(v_x_967_, 4);
lean_inc_ref_n(v_cmp_965_, 2);
v_val_971_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_965_, v_x_966_, v_lchild_968_);
v___x_972_ = l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(v_cmp_965_, v_key_969_, v_val_971_);
v_x_966_ = v___x_972_;
v_x_967_ = v_rchild_970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_diff___redArg(lean_object* v_cmp_974_, lean_object* v_t_u2081_975_, lean_object* v_t_u2082_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_974_, v_t_u2081_975_, v_t_u2082_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_diff(lean_object* v_00_u03b1_978_, lean_object* v_cmp_979_, lean_object* v_t_u2081_980_, lean_object* v_t_u2082_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_979_, v_t_u2081_980_, v_t_u2082_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0(lean_object* v_00_u03b1_983_, lean_object* v_cmp_984_, lean_object* v_00_u03b2_985_, lean_object* v_x_986_, lean_object* v_t_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0___redArg(v_cmp_984_, v_x_986_, v_t_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1(lean_object* v_00_u03b1_989_, lean_object* v_cmp_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_RBNode_fold___at___00Lean_RBTree_diff_spec__1___redArg(v_cmp_990_, v_x_991_, v_x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0(lean_object* v_00_u03b1_994_, lean_object* v_cmp_995_, lean_object* v_00_u03b2_996_, lean_object* v_x_997_, lean_object* v_x_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_RBNode_del___at___00Lean_RBNode_erase___at___00Lean_RBTree_diff_spec__0_spec__0___redArg(v_cmp_995_, v_x_997_, v_x_998_);
return v___x_999_;
}
}
uint8_t l_Lean_RBTree_filter___redArg___lam__0(lean_object* v_f_1000_, lean_object* v_a_1001_, lean_object* v_x_1002_){
_start:
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = lean_apply_1(v_f_1000_, v_a_1001_);
v___x_1004_ = lean_unbox(v___x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT void l_Lean_RBTree_filter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1000_ = stack[0].m_obj;
lean_object* v_a_1001_ = stack[1].m_obj;
lean_object* v_x_1002_ = stack[2].m_obj;
uint8_t v_res_1005_;
v_res_1005_ = l_Lean_RBTree_filter___redArg___lam__0(v_f_1000_, v_a_1001_, v_x_1002_);
stack->m_num = v_res_1005_;
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg___lam__0___boxed(lean_object* v_f_1006_, lean_object* v_a_1007_, lean_object* v_x_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = l_Lean_RBTree_filter___redArg___lam__0(v_f_1006_, v_a_1007_, v_x_1008_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter___redArg(lean_object* v_cmp_1011_, lean_object* v_f_1012_, lean_object* v_m_1013_){
_start:
{
lean_object* v___f_1014_; lean_object* v___x_1015_; 
v___f_1014_ = lean_alloc_closure((void*)(l_Lean_RBTree_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1014_, 0, v_f_1012_);
v___x_1015_ = l_Lean_RBMap_filter___redArg(v_cmp_1011_, v___f_1014_, v_m_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_filter(lean_object* v_00_u03b1_1016_, lean_object* v_cmp_1017_, lean_object* v_f_1018_, lean_object* v_m_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_RBTree_filter___redArg(v_cmp_1017_, v_f_1018_, v_m_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbtreeOf___redArg(lean_object* v_l_1021_, lean_object* v_cmp_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_RBTree_fromList___redArg(v_l_1021_, v_cmp_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_rbtreeOf(lean_object* v_00_u03b1_1024_, lean_object* v_l_1025_, lean_object* v_cmp_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_RBTree_fromList___redArg(v_l_1025_, v_cmp_1026_);
return v___x_1027_;
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
