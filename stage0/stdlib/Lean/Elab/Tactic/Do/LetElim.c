// Lean compiler output
// Module: Lean.Elab.Tactic.Do.LetElim
// Imports: public import Lean.Meta.Tactic.Simp import Init.Omega
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
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_mergeBy(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isCharLit(lean_object*);
uint8_t l_Lean_Meta_Simp_isOfNatNatLit(lean_object*);
uint8_t l_Lean_Meta_Simp_isOfScientificLit(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instBEqUses_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instBEqUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instBEqUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instOrdUses_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instOrdUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instOrdUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instInhabitedUses_default;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instInhabitedUses;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_add(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Uses_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instAddUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instAddUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_FVarUses_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instAddFVarUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_addMData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_addMData___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_addMData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uses"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 67, 224, 192, 49, 118, 23, 147)}};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "BVar index out of bounds: "};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " >= "};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_Uses_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(lean_object* v_zero_24_){
_start:
{
lean_inc(v_zero_24_);
return v_zero_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(lean_object* v_zero_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(v_zero_25_);
lean_dec(v_zero_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_zero_30_){
_start:
{
lean_inc(v_zero_30_);
return v_zero_30_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_Uses_zero_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_zero_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_box(0), v_t_28_, lean_box(0), v_zero_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_zero_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_zero_35_);
lean_dec(v_zero_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(lean_object* v_one_38_){
_start:
{
lean_inc(v_one_38_);
return v_one_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(lean_object* v_one_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(v_one_39_);
lean_dec(v_one_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_one_44_){
_start:
{
lean_inc(v_one_44_);
return v_one_44_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_Uses_one_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_one_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_box(0), v_t_42_, lean_box(0), v_one_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_one_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Elab_Tactic_Do_Uses_one_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_one_49_);
lean_dec(v_one_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(lean_object* v_many_52_){
_start:
{
lean_inc(v_many_52_);
return v_many_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(lean_object* v_many_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(v_many_53_);
lean_dec(v_many_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_many_58_){
_start:
{
lean_inc(v_many_58_);
return v_many_58_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_Uses_many_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_many_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_box(0), v_t_56_, lean_box(0), v_many_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_many_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Elab_Tactic_Do_Uses_many_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_many_63_);
lean_dec(v_many_63_);
return v_res_65_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_instBEqUses_beq(uint8_t v_x_66_, uint8_t v_y_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_68_ = lean_box(v_x_66_);
v___x_69_ = lean_obj_tag_nat(v___x_68_);
lean_dec(v___x_68_);
v___x_70_ = lean_box(v_y_67_);
v___x_71_ = lean_obj_tag_nat(v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_nat_dec_eq(v___x_69_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_instBEqUses_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_66_ = stack[0].m_num;
uint8_t v_y_67_ = stack[1].m_num;
uint8_t v_res_73_;
v_res_73_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_x_66_, v_y_67_);
stack->m_num = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(lean_object* v_x_74_, lean_object* v_y_75_){
_start:
{
uint8_t v_x_24__boxed_76_; uint8_t v_y_25__boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v_x_24__boxed_76_ = lean_unbox(v_x_74_);
v_y_25__boxed_77_ = lean_unbox(v_y_75_);
v_res_78_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_x_24__boxed_76_, v_y_25__boxed_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_instOrdUses_ord(uint8_t v_x_82_, uint8_t v_y_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_84_ = lean_box(v_x_82_);
v___x_85_ = lean_obj_tag_nat(v___x_84_);
lean_dec(v___x_84_);
v___x_86_ = lean_box(v_y_83_);
v___x_87_ = lean_obj_tag_nat(v___x_86_);
lean_dec(v___x_86_);
v___x_88_ = lean_nat_dec_lt(v___x_85_, v___x_87_);
if (v___x_88_ == 0)
{
uint8_t v___x_89_; 
v___x_89_ = lean_nat_dec_eq(v___x_85_, v___x_87_);
if (v___x_89_ == 0)
{
uint8_t v___x_90_; 
v___x_90_ = 2;
return v___x_90_;
}
else
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_instOrdUses_ord_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_82_ = stack[0].m_num;
uint8_t v_y_83_ = stack[1].m_num;
uint8_t v_res_93_;
v_res_93_ = l_Lean_Elab_Tactic_Do_instOrdUses_ord(v_x_82_, v_y_83_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(lean_object* v_x_94_, lean_object* v_y_95_){
_start:
{
uint8_t v_x_33__boxed_96_; uint8_t v_y_34__boxed_97_; uint8_t v_res_98_; lean_object* v_r_99_; 
v_x_33__boxed_96_ = lean_unbox(v_x_94_);
v_y_34__boxed_97_ = lean_unbox(v_y_95_);
v_res_98_ = l_Lean_Elab_Tactic_Do_instOrdUses_ord(v_x_33__boxed_96_, v_y_34__boxed_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default(void){
_start:
{
uint8_t v___x_102_; 
v___x_102_ = 0;
return v___x_102_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses(void){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = 0;
return v___x_103_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_Uses_add(uint8_t v_x_104_, uint8_t v_x_105_){
_start:
{
if (v_x_104_ == 0)
{
return v_x_105_;
}
else
{
if (v_x_105_ == 0)
{
return v_x_104_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 2;
return v___x_106_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_Uses_add_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_104_ = stack[0].m_num;
uint8_t v_x_105_ = stack[1].m_num;
uint8_t v_res_107_;
v_res_107_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x_104_, v_x_105_);
stack->m_num = v_res_107_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_add___boxed(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
uint8_t v_x_18__boxed_110_; uint8_t v_x_19__boxed_111_; uint8_t v_res_112_; lean_object* v_r_113_; 
v_x_18__boxed_110_ = lean_unbox(v_x_108_);
v_x_19__boxed_111_ = lean_unbox(v_x_109_);
v_res_112_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x_18__boxed_110_, v_x_19__boxed_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat(uint8_t v_x_114_){
_start:
{
switch(v_x_114_)
{
case 0:
{
lean_object* v___x_115_; 
v___x_115_ = lean_unsigned_to_nat(0u);
return v___x_115_;
}
case 1:
{
lean_object* v___x_116_; 
v___x_116_ = lean_unsigned_to_nat(1u);
return v___x_116_;
}
default: 
{
lean_object* v___x_117_; 
v___x_117_ = lean_unsigned_to_nat(2u);
return v___x_117_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_Uses_toNat_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_114_ = stack[0].m_num;
lean_object* v_res_118_;
v_res_118_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v_x_114_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(lean_object* v_x_119_){
_start:
{
uint8_t v_x_34__boxed_120_; lean_object* v_res_121_; 
v_x_34__boxed_120_ = lean_unbox(v_x_119_);
v_res_121_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v_x_34__boxed_120_);
return v_res_121_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_Uses_fromNat(lean_object* v_x_122_){
_start:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_nat_dec_eq(v_x_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = lean_nat_dec_eq(v_x_122_, v___x_125_);
if (v___x_126_ == 0)
{
uint8_t v___x_127_; 
v___x_127_ = 2;
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 1;
return v___x_128_;
}
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
return v___x_129_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_Uses_fromNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_122_ = stack[0].m_obj;
uint8_t v_res_130_;
v_res_130_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v_x_122_);
stack->m_num = v_res_130_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(lean_object* v_x_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v_x_131_);
lean_dec(v_x_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
return v_x_136_;
}
else
{
lean_object* v_key_138_; lean_object* v_value_139_; lean_object* v_tail_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_163_; 
v_key_138_ = lean_ctor_get(v_x_137_, 0);
v_value_139_ = lean_ctor_get(v_x_137_, 1);
v_tail_140_ = lean_ctor_get(v_x_137_, 2);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_163_ == 0)
{
v___x_142_ = v_x_137_;
v_isShared_143_ = v_isSharedCheck_163_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_tail_140_);
lean_inc(v_value_139_);
lean_inc(v_key_138_);
lean_dec(v_x_137_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_163_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; uint64_t v___x_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v_fold_148_; uint64_t v___x_149_; uint64_t v___x_150_; uint64_t v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_144_ = lean_array_get_size(v_x_136_);
v___x_145_ = l_Lean_instHashableFVarId_hash(v_key_138_);
v___x_146_ = 32ULL;
v___x_147_ = lean_uint64_shift_right(v___x_145_, v___x_146_);
v_fold_148_ = lean_uint64_xor(v___x_145_, v___x_147_);
v___x_149_ = 16ULL;
v___x_150_ = lean_uint64_shift_right(v_fold_148_, v___x_149_);
v___x_151_ = lean_uint64_xor(v_fold_148_, v___x_150_);
v___x_152_ = lean_uint64_to_usize(v___x_151_);
v___x_153_ = lean_usize_of_nat(v___x_144_);
v___x_154_ = ((size_t)1ULL);
v___x_155_ = lean_usize_sub(v___x_153_, v___x_154_);
v___x_156_ = lean_usize_land(v___x_152_, v___x_155_);
v___x_157_ = lean_array_uget_borrowed(v_x_136_, v___x_156_);
lean_inc(v___x_157_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 2, v___x_157_);
v___x_159_ = v___x_142_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_key_138_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_value_139_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v___x_157_);
v___x_159_ = v_reuseFailAlloc_162_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; 
v___x_160_ = lean_array_uset(v_x_136_, v___x_156_, v___x_159_);
v_x_136_ = v___x_160_;
v_x_137_ = v_tail_140_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(lean_object* v_i_164_, lean_object* v_source_165_, lean_object* v_target_166_){
_start:
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_array_get_size(v_source_165_);
v___x_168_ = lean_nat_dec_lt(v_i_164_, v___x_167_);
if (v___x_168_ == 0)
{
lean_dec_ref(v_source_165_);
lean_dec(v_i_164_);
return v_target_166_;
}
else
{
lean_object* v_es_169_; lean_object* v___x_170_; lean_object* v_source_171_; lean_object* v_target_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_es_169_ = lean_array_fget(v_source_165_, v_i_164_);
v___x_170_ = lean_box(0);
v_source_171_ = lean_array_fset(v_source_165_, v_i_164_, v___x_170_);
v_target_172_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_target_166_, v_es_169_);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_i_164_, v___x_173_);
lean_dec(v_i_164_);
v_i_164_ = v___x_174_;
v_source_165_ = v_source_171_;
v_target_166_ = v_target_172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(lean_object* v_data_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_nbuckets_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_177_ = lean_array_get_size(v_data_176_);
v___x_178_ = lean_unsigned_to_nat(2u);
v_nbuckets_179_ = lean_nat_mul(v___x_177_, v___x_178_);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = lean_box(0);
v___x_182_ = lean_mk_array(v_nbuckets_179_, v___x_181_);
v___x_183_ = lean_array_propagate_mark(v_data_176_, v___x_182_);
v___x_184_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v___x_180_, v_data_176_, v___x_183_);
return v___x_184_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object* v_a_185_, lean_object* v_x_186_){
_start:
{
if (lean_obj_tag(v_x_186_) == 0)
{
uint8_t v___x_187_; 
v___x_187_ = 0;
return v___x_187_;
}
else
{
lean_object* v_key_188_; lean_object* v_tail_189_; uint8_t v___x_190_; 
v_key_188_ = lean_ctor_get(v_x_186_, 0);
v_tail_189_ = lean_ctor_get(v_x_186_, 2);
v___x_190_ = l_Lean_instBEqFVarId_beq(v_key_188_, v_a_185_);
if (v___x_190_ == 0)
{
v_x_186_ = v_tail_189_;
goto _start;
}
else
{
return v___x_190_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_185_ = stack[0].m_obj;
lean_object* v_x_186_ = stack[1].m_obj;
uint8_t v_res_192_;
v_res_192_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_185_, v_x_186_);
stack->m_num = v_res_192_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object* v_a_193_, lean_object* v_x_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_193_, v_x_194_);
lean_dec(v_x_194_);
lean_dec(v_a_193_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(uint8_t v_x3_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(v_x3_197_);
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_211_; 
v_val_201_ = lean_ctor_get(v_x_198_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_211_ == 0)
{
v___x_203_ = v_x_198_;
v_isShared_204_ = v_isSharedCheck_211_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_val_201_);
lean_dec(v_x_198_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_211_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
uint8_t v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_205_ = lean_unbox(v_val_201_);
lean_dec(v_val_201_);
v___x_206_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x3_197_, v___x_205_);
v___x_207_ = lean_box(v___x_206_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_207_);
v___x_209_ = v___x_203_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x3_197_ = stack[0].m_num;
lean_object* v_x_198_ = stack[1].m_obj;
lean_object* v_res_212_;
v_res_212_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_197_, v_x_198_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(lean_object* v_x3_213_, lean_object* v_x_214_){
_start:
{
uint8_t v_x3_902__boxed_215_; lean_object* v_res_216_; 
v_x3_902__boxed_215_ = lean_unbox(v_x3_213_);
v_res_216_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_902__boxed_215_, v_x_214_);
return v_res_216_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(uint8_t v_x3_217_, lean_object* v_a_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_val_222_; lean_object* v___x_223_; 
v___x_220_ = lean_box(0);
v___x_221_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_217_, v___x_220_);
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec(v___x_221_);
v___x_223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_223_, 0, v_a_218_);
lean_ctor_set(v___x_223_, 1, v_val_222_);
lean_ctor_set(v___x_223_, 2, v_x_219_);
return v___x_223_;
}
else
{
lean_object* v_key_224_; lean_object* v_value_225_; lean_object* v_tail_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_241_; 
v_key_224_ = lean_ctor_get(v_x_219_, 0);
v_value_225_ = lean_ctor_get(v_x_219_, 1);
v_tail_226_ = lean_ctor_get(v_x_219_, 2);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_241_ == 0)
{
v___x_228_ = v_x_219_;
v_isShared_229_ = v_isSharedCheck_241_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_tail_226_);
lean_inc(v_value_225_);
lean_inc(v_key_224_);
lean_dec(v_x_219_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_241_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
uint8_t v___x_230_; 
v___x_230_ = l_Lean_instBEqFVarId_beq(v_key_224_, v_a_218_);
if (v___x_230_ == 0)
{
lean_object* v_tail_231_; lean_object* v___x_233_; 
v_tail_231_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_217_, v_a_218_, v_tail_226_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 2, v_tail_231_);
v___x_233_ = v___x_228_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_key_224_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_value_225_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_tail_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_val_237_; lean_object* v___x_239_; 
lean_dec(v_key_224_);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v_value_225_);
v___x_236_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_217_, v___x_235_);
v_val_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_237_);
lean_dec(v___x_236_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v_val_237_);
lean_ctor_set(v___x_228_, 0, v_a_218_);
v___x_239_ = v___x_228_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_218_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_val_237_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_tail_226_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_x3_217_ = stack[0].m_num;
lean_object* v_a_218_ = stack[1].m_obj;
lean_object* v_x_219_ = stack[2].m_obj;
lean_object* v_res_242_;
v_res_242_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_217_, v_a_218_, v_x_219_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(lean_object* v_x3_243_, lean_object* v_a_244_, lean_object* v_x_245_){
_start:
{
uint8_t v_x3_951__boxed_246_; lean_object* v_res_247_; 
v_x3_951__boxed_246_ = lean_unbox(v_x3_243_);
v_res_247_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_951__boxed_246_, v_a_244_, v_x_245_);
return v_res_247_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(uint8_t v_x3_248_, lean_object* v_m_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_size_251_; lean_object* v_buckets_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_301_; 
v_size_251_ = lean_ctor_get(v_m_249_, 0);
v_buckets_252_ = lean_ctor_get(v_m_249_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v_m_249_);
if (v_isSharedCheck_301_ == 0)
{
v___x_254_ = v_m_249_;
v_isShared_255_ = v_isSharedCheck_301_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_buckets_252_);
lean_inc(v_size_251_);
lean_dec(v_m_249_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_301_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; uint64_t v___x_259_; uint64_t v_fold_260_; uint64_t v___x_261_; uint64_t v___x_262_; uint64_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; lean_object* v_bkt_269_; uint8_t v___x_270_; 
v___x_256_ = lean_array_get_size(v_buckets_252_);
v___x_257_ = l_Lean_instHashableFVarId_hash(v_a_250_);
v___x_258_ = 32ULL;
v___x_259_ = lean_uint64_shift_right(v___x_257_, v___x_258_);
v_fold_260_ = lean_uint64_xor(v___x_257_, v___x_259_);
v___x_261_ = 16ULL;
v___x_262_ = lean_uint64_shift_right(v_fold_260_, v___x_261_);
v___x_263_ = lean_uint64_xor(v_fold_260_, v___x_262_);
v___x_264_ = lean_uint64_to_usize(v___x_263_);
v___x_265_ = lean_usize_of_nat(v___x_256_);
v___x_266_ = ((size_t)1ULL);
v___x_267_ = lean_usize_sub(v___x_265_, v___x_266_);
v___x_268_ = lean_usize_land(v___x_264_, v___x_267_);
v_bkt_269_ = lean_array_uget_borrowed(v_buckets_252_, v___x_268_);
v___x_270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_250_, v_bkt_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v_size_x27_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_buckets_x27_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_271_ = lean_unsigned_to_nat(1u);
v_size_x27_272_ = lean_nat_add(v_size_251_, v___x_271_);
lean_dec(v_size_251_);
v___x_273_ = lean_box(v_x3_248_);
lean_inc(v_bkt_269_);
v___x_274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_274_, 0, v_a_250_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
lean_ctor_set(v___x_274_, 2, v_bkt_269_);
v_buckets_x27_275_ = lean_array_uset(v_buckets_252_, v___x_268_, v___x_274_);
v___x_276_ = lean_unsigned_to_nat(4u);
v___x_277_ = lean_nat_mul(v_size_x27_272_, v___x_276_);
v___x_278_ = lean_unsigned_to_nat(3u);
v___x_279_ = lean_nat_div(v___x_277_, v___x_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_array_get_size(v_buckets_x27_275_);
v___x_281_ = lean_nat_dec_le(v___x_279_, v___x_280_);
lean_dec(v___x_279_);
if (v___x_281_ == 0)
{
lean_object* v_val_282_; lean_object* v___x_284_; 
v_val_282_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_275_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_val_282_);
lean_ctor_set(v___x_254_, 0, v_size_x27_272_);
v___x_284_ = v___x_254_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_size_x27_272_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_val_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
else
{
lean_object* v___x_287_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_buckets_x27_275_);
lean_ctor_set(v___x_254_, 0, v_size_x27_272_);
v___x_287_ = v___x_254_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_size_x27_272_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_buckets_x27_275_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
else
{
lean_object* v___x_289_; lean_object* v_buckets_x27_290_; lean_object* v_bkt_x27_291_; lean_object* v___y_293_; uint8_t v___x_298_; 
lean_inc(v_bkt_269_);
v___x_289_ = lean_box(0);
v_buckets_x27_290_ = lean_array_uset(v_buckets_252_, v___x_268_, v___x_289_);
lean_inc(v_a_250_);
v_bkt_x27_291_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_248_, v_a_250_, v_bkt_269_);
v___x_298_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_250_, v_bkt_x27_291_);
lean_dec(v_a_250_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_sub(v_size_251_, v___x_299_);
lean_dec(v_size_251_);
v___y_293_ = v___x_300_;
goto v___jp_292_;
}
else
{
v___y_293_ = v_size_251_;
goto v___jp_292_;
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_array_uset(v_buckets_x27_290_, v___x_268_, v_bkt_x27_291_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_294_);
lean_ctor_set(v___x_254_, 0, v___y_293_);
v___x_296_ = v___x_254_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___y_293_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x3_248_ = stack[0].m_num;
lean_object* v_m_249_ = stack[1].m_obj;
lean_object* v_a_250_ = stack[2].m_obj;
lean_object* v_res_302_;
v_res_302_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v_x3_248_, v_m_249_, v_a_250_);
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object* v_x3_303_, lean_object* v_m_304_, lean_object* v_a_305_){
_start:
{
uint8_t v_x3_1024__boxed_306_; lean_object* v_res_307_; 
v_x3_1024__boxed_306_ = lean_unbox(v_x3_303_);
v_res_307_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v_x3_1024__boxed_306_, v_m_304_, v_a_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
return v_x_308_;
}
else
{
lean_object* v_key_310_; lean_object* v_value_311_; lean_object* v_tail_312_; uint8_t v___x_313_; lean_object* v___x_314_; 
v_key_310_ = lean_ctor_get(v_x_309_, 0);
lean_inc(v_key_310_);
v_value_311_ = lean_ctor_get(v_x_309_, 1);
lean_inc(v_value_311_);
v_tail_312_ = lean_ctor_get(v_x_309_, 2);
lean_inc(v_tail_312_);
lean_dec_ref_known(v_x_309_, 3);
v___x_313_ = lean_unbox(v_value_311_);
lean_dec(v_value_311_);
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v___x_313_, v_x_308_, v_key_310_);
v_x_308_ = v___x_314_;
v_x_309_ = v_tail_312_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object* v_as_316_, size_t v_i_317_, size_t v_stop_318_, lean_object* v_b_319_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = lean_usize_dec_eq(v_i_317_, v_stop_318_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; size_t v___x_323_; size_t v___x_324_; 
v___x_321_ = lean_array_uget_borrowed(v_as_316_, v_i_317_);
lean_inc(v___x_321_);
v___x_322_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(v_b_319_, v___x_321_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_add(v_i_317_, v___x_323_);
v_i_317_ = v___x_324_;
v_b_319_ = v___x_322_;
goto _start;
}
else
{
return v_b_319_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_316_ = stack[0].m_obj;
size_t v_i_317_ = stack[1].m_num;
size_t v_stop_318_ = stack[2].m_num;
lean_object* v_b_319_ = stack[3].m_obj;
lean_object* v_res_326_;
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_as_316_, v_i_317_, v_stop_318_, v_b_319_);
stack->m_obj
 = v_res_326_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object* v_as_327_, lean_object* v_i_328_, lean_object* v_stop_329_, lean_object* v_b_330_){
_start:
{
size_t v_i_boxed_331_; size_t v_stop_boxed_332_; lean_object* v_res_333_; 
v_i_boxed_331_ = lean_unbox_usize(v_i_328_);
lean_dec(v_i_328_);
v_stop_boxed_332_ = lean_unbox_usize(v_stop_329_);
lean_dec(v_stop_329_);
v_res_333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_as_327_, v_i_boxed_331_, v_stop_boxed_332_, v_b_330_);
lean_dec_ref(v_as_327_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object* v_a_334_, lean_object* v_b_335_){
_start:
{
lean_object* v_buckets_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_buckets_336_ = lean_ctor_get(v_a_334_, 1);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_array_get_size(v_buckets_336_);
v___x_339_ = lean_nat_dec_lt(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
return v_b_335_;
}
else
{
size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((size_t)0ULL);
v___x_341_ = lean_usize_of_nat(v___x_338_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_336_, v___x_340_, v___x_341_, v_b_335_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object* v_a_343_, lean_object* v_b_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_a_343_, v_b_344_);
lean_dec_ref(v_a_343_);
return v_res_345_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object* v_00_u03b2_346_, lean_object* v_a_347_, lean_object* v_x_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_347_, v_x_348_);
return v___x_349_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_347_ = stack[1].m_obj;
lean_object* v_x_348_ = stack[2].m_obj;
uint8_t v_res_350_;
v_res_350_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_box(0), v_a_347_, v_x_348_);
stack->m_num = v_res_350_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_351_, lean_object* v_a_352_, lean_object* v_x_353_){
_start:
{
uint8_t v_res_354_; lean_object* v_r_355_; 
v_res_354_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(v_00_u03b2_351_, v_a_352_, v_x_353_);
lean_dec(v_x_353_);
lean_dec(v_a_352_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(lean_object* v_00_u03b2_356_, lean_object* v_data_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_data_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_359_, lean_object* v_i_360_, lean_object* v_source_361_, lean_object* v_target_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v_i_360_, v_source_361_, v_target_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_x_365_, v_x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___redArg(lean_object* v_x_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_obj_tag_nat(v_x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___redArg___boxed(lean_object* v_x_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___redArg(v_x_372_);
lean_dec(v_x_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl(lean_object* v_n_374_, lean_object* v_x_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_tag_nat(v_x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl___boxed(lean_object* v_n_377_, lean_object* v_x_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___impl(v_n_377_, v_x_378_);
lean_dec(v_x_378_);
lean_dec(v_n_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object* v_t_380_, lean_object* v_k_381_){
_start:
{
if (lean_obj_tag(v_t_380_) == 0)
{
return v_k_381_;
}
else
{
lean_object* v_uses_382_; lean_object* v___x_383_; 
v_uses_382_ = lean_ctor_get(v_t_380_, 0);
lean_inc_ref(v_uses_382_);
lean_dec_ref_known(v_t_380_, 1);
v___x_383_ = lean_apply_1(v_k_381_, v_uses_382_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object* v_n_384_, lean_object* v_motive_385_, lean_object* v_ctorIdx_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_k_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_387_, v_k_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object* v_n_391_, lean_object* v_motive_392_, lean_object* v_ctorIdx_393_, lean_object* v_t_394_, lean_object* v_h_395_, lean_object* v_k_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(v_n_391_, v_motive_392_, v_ctorIdx_393_, v_t_394_, v_h_395_, v_k_396_);
lean_dec(v_ctorIdx_393_);
lean_dec(v_n_391_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object* v_t_398_, lean_object* v_none_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_398_, v_none_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object* v_n_401_, lean_object* v_motive_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_none_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_403_, v_none_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object* v_n_407_, lean_object* v_motive_408_, lean_object* v_t_409_, lean_object* v_h_410_, lean_object* v_none_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Elab_Tactic_Do_BVarUses_none_elim(v_n_407_, v_motive_408_, v_t_409_, v_h_410_, v_none_411_);
lean_dec(v_n_407_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object* v_t_413_, lean_object* v_some_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_413_, v_some_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object* v_n_416_, lean_object* v_motive_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_some_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_418_, v_some_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object* v_n_422_, lean_object* v_motive_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_some_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Elab_Tactic_Do_BVarUses_some_elim(v_n_422_, v_motive_423_, v_t_424_, v_h_425_, v_some_426_);
lean_dec(v_n_422_);
return v_res_427_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12));
v___x_453_ = l_Lean_mkAtom(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13);
v___x_455_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_456_ = lean_array_push(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_457_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14);
v___x_458_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11));
v___x_459_ = lean_box(2);
v___x_460_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
lean_ctor_set(v___x_460_, 2, v___x_457_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15);
v___x_462_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_463_ = lean_array_push(v___x_462_, v___x_461_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_464_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16);
v___x_465_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9));
v___x_466_ = lean_box(2);
v___x_467_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
lean_ctor_set(v___x_467_, 2, v___x_464_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17);
v___x_469_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_470_ = lean_array_push(v___x_469_, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_471_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18);
v___x_472_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7));
v___x_473_ = lean_box(2);
v___x_474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
lean_ctor_set(v___x_474_, 2, v___x_471_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19);
v___x_476_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_477_ = lean_array_push(v___x_476_, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_478_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20);
v___x_479_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4));
v___x_480_ = lean_box(2);
v___x_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
lean_ctor_set(v___x_481_, 2, v___x_478_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1(void){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21);
return v___x_482_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object* v_numBVars_483_, lean_object* v_n_484_, lean_object* v_i_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_sub(v_numBVars_483_, v___x_486_);
v___x_488_ = lean_nat_sub(v___x_487_, v_n_484_);
lean_dec(v___x_487_);
v___x_489_ = lean_nat_dec_eq(v_i_485_, v___x_488_);
lean_dec(v___x_488_);
if (v___x_489_ == 0)
{
uint8_t v___x_490_; 
v___x_490_ = 0;
return v___x_490_;
}
else
{
uint8_t v___x_491_; 
v___x_491_ = 1;
return v___x_491_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_numBVars_483_ = stack[0].m_obj;
lean_object* v_n_484_ = stack[1].m_obj;
lean_object* v_i_485_ = stack[2].m_obj;
uint8_t v_res_492_;
v_res_492_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(v_numBVars_483_, v_n_484_, v_i_485_);
stack->m_num = v_res_492_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object* v_numBVars_493_, lean_object* v_n_494_, lean_object* v_i_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(v_numBVars_493_, v_n_494_, v_i_495_);
lean_dec(v_i_495_);
lean_dec(v_n_494_);
lean_dec(v_numBVars_493_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object* v_numBVars_498_, lean_object* v_n_499_){
_start:
{
lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_inc(v_numBVars_498_);
v___f_500_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_500_, 0, v_numBVars_498_);
lean_closure_set(v___f_500_, 1, v_n_499_);
v___x_501_ = l_Array_ofFn___redArg(v_numBVars_498_, v___f_500_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object* v_numBVars_503_, lean_object* v_n_504_, lean_object* v_x_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(v_numBVars_503_, v_n_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object* v_numBVars_511_, lean_object* v_x_512_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v___x_513_; 
v___x_513_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0));
return v___x_513_;
}
else
{
lean_object* v_uses_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_527_; 
v_uses_514_ = lean_ctor_get(v_x_512_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_527_ == 0)
{
v___x_516_ = v_x_512_;
v_isShared_517_ = v_isSharedCheck_527_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_uses_514_);
lean_dec(v_x_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_527_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_numBVars_511_, v___x_518_);
v___x_520_ = lean_nat_sub(v___x_519_, v___x_518_);
lean_dec(v___x_519_);
v___x_521_ = lean_array_fget(v_uses_514_, v___x_520_);
lean_dec(v___x_520_);
v___x_522_ = lean_array_pop(v_uses_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_522_);
v___x_524_ = v___x_516_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_526_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_521_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object* v_numBVars_528_, lean_object* v_x_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Elab_Tactic_Do_BVarUses_pop(v_numBVars_528_, v_x_529_);
lean_dec(v_numBVars_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object* v_as_531_, lean_object* v_bs_532_, lean_object* v_i_533_, lean_object* v_cs_534_){
_start:
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_array_get_size(v_as_531_);
v___x_536_ = lean_nat_dec_lt(v_i_533_, v___x_535_);
if (v___x_536_ == 0)
{
lean_dec(v_i_533_);
return v_cs_534_;
}
else
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = lean_array_get_size(v_bs_532_);
v___x_538_ = lean_nat_dec_lt(v_i_533_, v___x_537_);
if (v___x_538_ == 0)
{
lean_dec(v_i_533_);
return v_cs_534_;
}
else
{
lean_object* v_a_539_; lean_object* v_b_540_; uint8_t v___x_541_; uint8_t v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_a_539_ = lean_array_fget_borrowed(v_as_531_, v_i_533_);
v_b_540_ = lean_array_fget_borrowed(v_bs_532_, v_i_533_);
v___x_541_ = lean_unbox(v_a_539_);
v___x_542_ = lean_unbox(v_b_540_);
v___x_543_ = l_Lean_Elab_Tactic_Do_Uses_add(v___x_541_, v___x_542_);
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_nat_add(v_i_533_, v___x_544_);
lean_dec(v_i_533_);
v___x_546_ = lean_box(v___x_543_);
v___x_547_ = lean_array_push(v_cs_534_, v___x_546_);
v_i_533_ = v___x_545_;
v_cs_534_ = v___x_547_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object* v_as_549_, lean_object* v_bs_550_, lean_object* v_i_551_, lean_object* v_cs_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_as_549_, v_bs_550_, v_i_551_, v_cs_552_);
lean_dec_ref(v_bs_550_);
lean_dec_ref(v_as_549_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object* v_a_556_, lean_object* v_b_557_){
_start:
{
if (lean_obj_tag(v_a_556_) == 0)
{
return v_b_557_;
}
else
{
if (lean_obj_tag(v_b_557_) == 0)
{
lean_object* v_uses_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
v_uses_558_ = lean_ctor_get(v_a_556_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_a_556_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v_a_556_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_uses_558_);
lean_dec(v_a_556_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_uses_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
else
{
lean_object* v_uses_566_; lean_object* v_uses_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_577_; 
v_uses_566_ = lean_ctor_get(v_a_556_, 0);
lean_inc_ref(v_uses_566_);
lean_dec_ref_known(v_a_556_, 1);
v_uses_567_ = lean_ctor_get(v_b_557_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_b_557_);
if (v_isSharedCheck_577_ == 0)
{
v___x_569_ = v_b_557_;
v_isShared_570_ = v_isSharedCheck_577_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_uses_567_);
lean_dec(v_b_557_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_577_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0));
v___x_573_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_uses_566_, v_uses_567_, v___x_571_, v___x_572_);
lean_dec_ref(v_uses_567_);
lean_dec_ref(v_uses_566_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_573_);
v___x_575_ = v___x_569_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object* v_numBVars_578_, lean_object* v_a_579_, lean_object* v_b_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(v_a_579_, v_b_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object* v_numBVars_582_, lean_object* v_a_583_, lean_object* v_b_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Elab_Tactic_Do_BVarUses_add(v_numBVars_582_, v_a_583_, v_b_584_);
lean_dec(v_numBVars_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object* v_numBVars_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_add___boxed), 3, 1);
lean_closure_set(v___x_587_, 0, v_numBVars_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object* v_f_588_, lean_object* v_x_589_){
_start:
{
lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_fst_590_ = lean_ctor_get(v_x_589_, 0);
v_snd_591_ = lean_ctor_get(v_x_589_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v_x_589_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_snd_591_);
lean_inc(v_fst_590_);
lean_dec(v_x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = lean_apply_1(v_f_588_, v_fst_590_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_snd_591_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object* v_00_u03b1_u2081_600_, lean_object* v_00_u03b1_u2082_601_, lean_object* v_00_u03b2_602_, lean_object* v_f_603_, lean_object* v_x_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v_f_603_, v_x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object* v_x_606_, lean_object* v_new_607_, lean_object* v_x_608_){
_start:
{
lean_inc_ref(v_new_607_);
return v_new_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object* v_x_609_, lean_object* v_new_610_, lean_object* v_x_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Elab_Tactic_Do_addMData___lam__0(v_x_609_, v_new_610_, v_x_611_);
lean_dec_ref(v_x_611_);
lean_dec_ref(v_new_610_);
lean_dec(v_x_609_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object* v_d_614_, lean_object* v_e_615_){
_start:
{
if (lean_obj_tag(v_e_615_) == 10)
{
lean_object* v_data_616_; lean_object* v_expr_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_data_616_ = lean_ctor_get(v_e_615_, 0);
lean_inc(v_data_616_);
v_expr_617_ = lean_ctor_get(v_e_615_, 1);
lean_inc_ref(v_expr_617_);
lean_dec_ref_known(v_e_615_, 2);
v___f_618_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_addMData___closed__0));
v___x_619_ = l_Lean_KVMap_mergeBy(v___f_618_, v_d_614_, v_data_616_);
lean_dec(v_data_616_);
v___x_620_ = l_Lean_Expr_mdata___override(v___x_619_, v_expr_617_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Expr_mdata___override(v_d_614_, v_e_615_);
return v___x_621_;
}
}
}
uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object* v_e_622_){
_start:
{
uint8_t v___y_624_; 
switch(lean_obj_tag(v_e_622_))
{
case 1:
{
uint8_t v___x_626_; 
v___x_626_ = 0;
return v___x_626_;
}
case 5:
{
uint8_t v___x_627_; 
v___x_627_ = l_Lean_Meta_Simp_isOfNatNatLit(v_e_622_);
if (v___x_627_ == 0)
{
uint8_t v___x_628_; 
v___x_628_ = l_Lean_Meta_Simp_isOfScientificLit(v_e_622_);
v___y_624_ = v___x_628_;
goto v___jp_623_;
}
else
{
v___y_624_ = v___x_627_;
goto v___jp_623_;
}
}
case 6:
{
uint8_t v___x_629_; 
v___x_629_ = 0;
return v___x_629_;
}
case 7:
{
uint8_t v___x_630_; 
v___x_630_ = 0;
return v___x_630_;
}
case 8:
{
uint8_t v___x_631_; 
v___x_631_ = 0;
return v___x_631_;
}
case 10:
{
lean_object* v_expr_632_; 
v_expr_632_ = lean_ctor_get(v_e_622_, 1);
v_e_622_ = v_expr_632_;
goto _start;
}
case 11:
{
lean_object* v_struct_634_; 
v_struct_634_ = lean_ctor_get(v_e_622_, 2);
v_e_622_ = v_struct_634_;
goto _start;
}
default: 
{
uint8_t v___x_636_; 
v___x_636_ = 1;
return v___x_636_;
}
}
v___jp_623_:
{
if (v___y_624_ == 0)
{
uint8_t v___x_625_; 
v___x_625_ = l_Lean_Meta_Simp_isCharLit(v_e_622_);
return v___x_625_;
}
else
{
return v___y_624_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_622_ = stack[0].m_obj;
uint8_t v_res_637_;
v_res_637_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_e_622_);
stack->m_num = v_res_637_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object* v_e_638_){
_start:
{
uint8_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_e_638_);
lean_dec_ref(v_e_638_);
v_r_640_ = lean_box(v_res_639_);
return v_r_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object* v_val_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v_val_641_);
return v___x_642_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object* v_msgData_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v___x_649_; lean_object* v_env_650_; uint8_t v___x_651_; lean_object* v_env_652_; lean_object* v___x_653_; lean_object* v_toCold_654_; lean_object* v_mctx_655_; lean_object* v_lctx_656_; lean_object* v_options_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_649_ = lean_st_ref_get(v___y_647_);
v_env_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc_ref(v_env_650_);
lean_dec(v___x_649_);
v___x_651_ = 0;
v_env_652_ = l_Lean_Environment_setRecordingDeps(v_env_650_, v___x_651_);
v___x_653_ = lean_st_ref_get(v___y_645_);
v_toCold_654_ = lean_ctor_get(v___y_646_, 0);
v_mctx_655_ = lean_ctor_get(v___x_653_, 0);
lean_inc_ref(v_mctx_655_);
lean_dec(v___x_653_);
v_lctx_656_ = lean_ctor_get(v___y_644_, 2);
v_options_657_ = lean_ctor_get(v_toCold_654_, 2);
lean_inc_ref(v_options_657_);
lean_inc_ref(v_lctx_656_);
v___x_658_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_658_, 0, v_env_652_);
lean_ctor_set(v___x_658_, 1, v_mctx_655_);
lean_ctor_set(v___x_658_, 2, v_lctx_656_);
lean_ctor_set(v___x_658_, 3, v_options_657_);
v___x_659_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v_msgData_643_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_643_ = stack[0].m_obj;
lean_object* v___y_644_ = stack[1].m_obj;
lean_object* v___y_645_ = stack[2].m_obj;
lean_object* v___y_646_ = stack[3].m_obj;
lean_object* v___y_647_ = stack[4].m_obj;
lean_object* v_res_661_;
v_res_661_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
stack->m_obj
 = v_res_661_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object* v_msgData_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_668_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_ref_675_; lean_object* v___x_676_; lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_685_; 
v_ref_675_ = lean_ctor_get(v___y_672_, 2);
v___x_676_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msg_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
v_a_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_685_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_683_; 
lean_inc(v_ref_675_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_ref_675_);
lean_ctor_set(v___x_681_, 1, v_a_677_);
if (v_isShared_680_ == 0)
{
lean_ctor_set_tag(v___x_679_, 1);
lean_ctor_set(v___x_679_, 0, v___x_681_);
v___x_683_ = v___x_679_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_669_ = stack[0].m_obj;
lean_object* v___y_670_ = stack[1].m_obj;
lean_object* v___y_671_ = stack[2].m_obj;
lean_object* v___y_672_ = stack[3].m_obj;
lean_object* v___y_673_ = stack[4].m_obj;
lean_object* v_res_686_;
v_res_686_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
stack->m_obj
 = v_res_686_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object* v_msg_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object* v_data_694_, lean_object* v_expr_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_Expr_mdata___override(v_data_694_, v_expr_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object* v_typeName_697_, lean_object* v_idx_698_, lean_object* v_struct_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_Expr_proj___override(v_typeName_697_, v_idx_698_, v_struct_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object* v_a_701_, lean_object* v_b_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_dec(v_b_702_);
lean_dec(v_a_701_);
return v_x_703_;
}
else
{
lean_object* v_key_704_; lean_object* v_value_705_; lean_object* v_tail_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_718_; 
v_key_704_ = lean_ctor_get(v_x_703_, 0);
v_value_705_ = lean_ctor_get(v_x_703_, 1);
v_tail_706_ = lean_ctor_get(v_x_703_, 2);
v_isSharedCheck_718_ = !lean_is_exclusive(v_x_703_);
if (v_isSharedCheck_718_ == 0)
{
v___x_708_ = v_x_703_;
v_isShared_709_ = v_isSharedCheck_718_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_tail_706_);
lean_inc(v_value_705_);
lean_inc(v_key_704_);
lean_dec(v_x_703_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_718_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
uint8_t v___x_710_; 
v___x_710_ = l_Lean_instBEqFVarId_beq(v_key_704_, v_a_701_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_701_, v_b_702_, v_tail_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 2, v___x_711_);
v___x_713_ = v___x_708_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_key_704_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_value_705_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
else
{
lean_object* v___x_716_; 
lean_dec(v_value_705_);
lean_dec(v_key_704_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v_b_702_);
lean_ctor_set(v___x_708_, 0, v_a_701_);
v___x_716_ = v___x_708_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_701_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_b_702_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_tail_706_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object* v_m_719_, lean_object* v_a_720_, lean_object* v_b_721_){
_start:
{
lean_object* v_size_722_; lean_object* v_buckets_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_766_; 
v_size_722_ = lean_ctor_get(v_m_719_, 0);
v_buckets_723_ = lean_ctor_get(v_m_719_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_m_719_);
if (v_isSharedCheck_766_ == 0)
{
v___x_725_ = v_m_719_;
v_isShared_726_ = v_isSharedCheck_766_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_buckets_723_);
lean_inc(v_size_722_);
lean_dec(v_m_719_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_766_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; uint64_t v___x_728_; uint64_t v___x_729_; uint64_t v___x_730_; uint64_t v_fold_731_; uint64_t v___x_732_; uint64_t v___x_733_; uint64_t v___x_734_; size_t v___x_735_; size_t v___x_736_; size_t v___x_737_; size_t v___x_738_; size_t v___x_739_; lean_object* v_bkt_740_; uint8_t v___x_741_; 
v___x_727_ = lean_array_get_size(v_buckets_723_);
v___x_728_ = l_Lean_instHashableFVarId_hash(v_a_720_);
v___x_729_ = 32ULL;
v___x_730_ = lean_uint64_shift_right(v___x_728_, v___x_729_);
v_fold_731_ = lean_uint64_xor(v___x_728_, v___x_730_);
v___x_732_ = 16ULL;
v___x_733_ = lean_uint64_shift_right(v_fold_731_, v___x_732_);
v___x_734_ = lean_uint64_xor(v_fold_731_, v___x_733_);
v___x_735_ = lean_uint64_to_usize(v___x_734_);
v___x_736_ = lean_usize_of_nat(v___x_727_);
v___x_737_ = ((size_t)1ULL);
v___x_738_ = lean_usize_sub(v___x_736_, v___x_737_);
v___x_739_ = lean_usize_land(v___x_735_, v___x_738_);
v_bkt_740_ = lean_array_uget_borrowed(v_buckets_723_, v___x_739_);
v___x_741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_720_, v_bkt_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v_size_x27_743_; lean_object* v___x_744_; lean_object* v_buckets_x27_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_742_ = lean_unsigned_to_nat(1u);
v_size_x27_743_ = lean_nat_add(v_size_722_, v___x_742_);
lean_dec(v_size_722_);
lean_inc(v_bkt_740_);
v___x_744_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_744_, 0, v_a_720_);
lean_ctor_set(v___x_744_, 1, v_b_721_);
lean_ctor_set(v___x_744_, 2, v_bkt_740_);
v_buckets_x27_745_ = lean_array_uset(v_buckets_723_, v___x_739_, v___x_744_);
v___x_746_ = lean_unsigned_to_nat(4u);
v___x_747_ = lean_nat_mul(v_size_x27_743_, v___x_746_);
v___x_748_ = lean_unsigned_to_nat(3u);
v___x_749_ = lean_nat_div(v___x_747_, v___x_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_array_get_size(v_buckets_x27_745_);
v___x_751_ = lean_nat_dec_le(v___x_749_, v___x_750_);
lean_dec(v___x_749_);
if (v___x_751_ == 0)
{
lean_object* v_val_752_; lean_object* v___x_754_; 
v_val_752_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_745_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v_val_752_);
lean_ctor_set(v___x_725_, 0, v_size_x27_743_);
v___x_754_ = v___x_725_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_size_x27_743_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_val_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
lean_object* v___x_757_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v_buckets_x27_745_);
lean_ctor_set(v___x_725_, 0, v_size_x27_743_);
v___x_757_ = v___x_725_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_size_x27_743_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_buckets_x27_745_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v___x_759_; lean_object* v_buckets_x27_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
lean_inc(v_bkt_740_);
v___x_759_ = lean_box(0);
v_buckets_x27_760_ = lean_array_uset(v_buckets_723_, v___x_739_, v___x_759_);
v___x_761_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_720_, v_b_721_, v_bkt_740_);
v___x_762_ = lean_array_uset(v_buckets_x27_760_, v___x_739_, v___x_761_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v___x_762_);
v___x_764_ = v___x_725_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_size_722_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; lean_object* v_ngen_770_; lean_object* v_namePrefix_771_; lean_object* v_idx_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_802_; 
v___x_769_ = lean_st_ref_get(v___y_767_);
v_ngen_770_ = lean_ctor_get(v___x_769_, 2);
lean_inc_ref(v_ngen_770_);
lean_dec(v___x_769_);
v_namePrefix_771_ = lean_ctor_get(v_ngen_770_, 0);
v_idx_772_ = lean_ctor_get(v_ngen_770_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_ngen_770_);
if (v_isSharedCheck_802_ == 0)
{
v___x_774_ = v_ngen_770_;
v_isShared_775_ = v_isSharedCheck_802_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_idx_772_);
lean_inc(v_namePrefix_771_);
lean_dec(v_ngen_770_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_802_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_r_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
lean_inc(v_idx_772_);
lean_inc(v_namePrefix_771_);
v_r_776_ = l_Lean_Name_num___override(v_namePrefix_771_, v_idx_772_);
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = lean_nat_add(v_idx_772_, v___x_777_);
lean_dec(v_idx_772_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_778_);
v___x_780_ = v___x_774_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_namePrefix_771_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_778_);
v___x_780_ = v_reuseFailAlloc_801_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v_env_782_; lean_object* v_nextMacroScope_783_; lean_object* v_auxDeclNGen_784_; lean_object* v_traceState_785_; lean_object* v_cache_786_; lean_object* v_recordedDeps_787_; lean_object* v_messages_788_; lean_object* v_infoState_789_; lean_object* v_snapshotTasks_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_799_; 
v___x_781_ = lean_st_ref_take(v___y_767_);
v_env_782_ = lean_ctor_get(v___x_781_, 0);
v_nextMacroScope_783_ = lean_ctor_get(v___x_781_, 1);
v_auxDeclNGen_784_ = lean_ctor_get(v___x_781_, 3);
v_traceState_785_ = lean_ctor_get(v___x_781_, 4);
v_cache_786_ = lean_ctor_get(v___x_781_, 5);
v_recordedDeps_787_ = lean_ctor_get(v___x_781_, 6);
v_messages_788_ = lean_ctor_get(v___x_781_, 7);
v_infoState_789_ = lean_ctor_get(v___x_781_, 8);
v_snapshotTasks_790_ = lean_ctor_get(v___x_781_, 9);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; 
v_unused_800_ = lean_ctor_get(v___x_781_, 2);
lean_dec(v_unused_800_);
v___x_792_ = v___x_781_;
v_isShared_793_ = v_isSharedCheck_799_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_snapshotTasks_790_);
lean_inc(v_infoState_789_);
lean_inc(v_messages_788_);
lean_inc(v_recordedDeps_787_);
lean_inc(v_cache_786_);
lean_inc(v_traceState_785_);
lean_inc(v_auxDeclNGen_784_);
lean_inc(v_nextMacroScope_783_);
lean_inc(v_env_782_);
lean_dec(v___x_781_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_799_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 2, v___x_780_);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_env_782_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_nextMacroScope_783_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_auxDeclNGen_784_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_traceState_785_);
lean_ctor_set(v_reuseFailAlloc_798_, 5, v_cache_786_);
lean_ctor_set(v_reuseFailAlloc_798_, 6, v_recordedDeps_787_);
lean_ctor_set(v_reuseFailAlloc_798_, 7, v_messages_788_);
lean_ctor_set(v_reuseFailAlloc_798_, 8, v_infoState_789_);
lean_ctor_set(v_reuseFailAlloc_798_, 9, v_snapshotTasks_790_);
v___x_795_ = v_reuseFailAlloc_798_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_st_ref_put(v___y_767_, v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v_r_776_);
return v___x_797_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_767_ = stack[0].m_obj;
lean_object* v_res_803_;
v_res_803_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_767_);
stack->m_obj
 = v_res_803_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_804_);
lean_dec(v___y_804_);
return v_res_806_;
}
}
lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
v___x_812_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_810_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_807_ = stack[0].m_obj;
lean_object* v___y_808_ = stack[1].m_obj;
lean_object* v___y_809_ = stack[2].m_obj;
lean_object* v___y_810_ = stack[3].m_obj;
lean_object* v_res_821_;
v_res_821_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v___y_807_, v___y_808_, v___y_809_, v___y_810_);
stack->m_obj
 = v_res_821_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object* v_a_828_, lean_object* v_x_829_){
_start:
{
if (lean_obj_tag(v_x_829_) == 0)
{
return v_x_829_;
}
else
{
lean_object* v_key_830_; lean_object* v_value_831_; lean_object* v_tail_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_841_; 
v_key_830_ = lean_ctor_get(v_x_829_, 0);
v_value_831_ = lean_ctor_get(v_x_829_, 1);
v_tail_832_ = lean_ctor_get(v_x_829_, 2);
v_isSharedCheck_841_ = !lean_is_exclusive(v_x_829_);
if (v_isSharedCheck_841_ == 0)
{
v___x_834_ = v_x_829_;
v_isShared_835_ = v_isSharedCheck_841_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_tail_832_);
lean_inc(v_value_831_);
lean_inc(v_key_830_);
lean_dec(v_x_829_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_841_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
uint8_t v___x_836_; 
v___x_836_ = l_Lean_instBEqFVarId_beq(v_key_830_, v_a_828_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_828_, v_tail_832_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 2, v___x_837_);
v___x_839_ = v___x_834_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_key_830_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_value_831_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
lean_del_object(v___x_834_);
lean_dec(v_value_831_);
lean_dec(v_key_830_);
return v_tail_832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object* v_a_842_, lean_object* v_x_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_842_, v_x_843_);
lean_dec(v_a_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object* v_m_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_size_847_; lean_object* v_buckets_848_; lean_object* v___x_849_; uint64_t v___x_850_; uint64_t v___x_851_; uint64_t v___x_852_; uint64_t v_fold_853_; uint64_t v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v___x_859_; size_t v___x_860_; size_t v___x_861_; lean_object* v_bkt_862_; uint8_t v___x_863_; 
v_size_847_ = lean_ctor_get(v_m_845_, 0);
v_buckets_848_ = lean_ctor_get(v_m_845_, 1);
v___x_849_ = lean_array_get_size(v_buckets_848_);
v___x_850_ = l_Lean_instHashableFVarId_hash(v_a_846_);
v___x_851_ = 32ULL;
v___x_852_ = lean_uint64_shift_right(v___x_850_, v___x_851_);
v_fold_853_ = lean_uint64_xor(v___x_850_, v___x_852_);
v___x_854_ = 16ULL;
v___x_855_ = lean_uint64_shift_right(v_fold_853_, v___x_854_);
v___x_856_ = lean_uint64_xor(v_fold_853_, v___x_855_);
v___x_857_ = lean_uint64_to_usize(v___x_856_);
v___x_858_ = lean_usize_of_nat(v___x_849_);
v___x_859_ = ((size_t)1ULL);
v___x_860_ = lean_usize_sub(v___x_858_, v___x_859_);
v___x_861_ = lean_usize_land(v___x_857_, v___x_860_);
v_bkt_862_ = lean_array_uget_borrowed(v_buckets_848_, v___x_861_);
v___x_863_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_846_, v_bkt_862_);
if (v___x_863_ == 0)
{
return v_m_845_;
}
else
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_876_; 
lean_inc(v_bkt_862_);
lean_inc_ref(v_buckets_848_);
lean_inc(v_size_847_);
v_isSharedCheck_876_ = !lean_is_exclusive(v_m_845_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; lean_object* v_unused_878_; 
v_unused_877_ = lean_ctor_get(v_m_845_, 1);
lean_dec(v_unused_877_);
v_unused_878_ = lean_ctor_get(v_m_845_, 0);
lean_dec(v_unused_878_);
v___x_865_ = v_m_845_;
v_isShared_866_ = v_isSharedCheck_876_;
goto v_resetjp_864_;
}
else
{
lean_dec(v_m_845_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_876_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v_buckets_x27_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_867_ = lean_box(0);
v_buckets_x27_868_ = lean_array_uset(v_buckets_848_, v___x_861_, v___x_867_);
v___x_869_ = lean_unsigned_to_nat(1u);
v___x_870_ = lean_nat_sub(v_size_847_, v___x_869_);
lean_dec(v_size_847_);
v___x_871_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_846_, v_bkt_862_);
v___x_872_ = lean_array_uset(v_buckets_x27_868_, v___x_861_, v___x_871_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v___x_872_);
lean_ctor_set(v___x_865_, 0, v___x_870_);
v___x_874_ = v___x_865_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object* v_m_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_879_, v_a_880_);
lean_dec(v_a_880_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object* v_a_882_, lean_object* v_fallback_883_, lean_object* v_x_884_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
lean_inc(v_fallback_883_);
return v_fallback_883_;
}
else
{
lean_object* v_key_885_; lean_object* v_value_886_; lean_object* v_tail_887_; uint8_t v___x_888_; 
v_key_885_ = lean_ctor_get(v_x_884_, 0);
v_value_886_ = lean_ctor_get(v_x_884_, 1);
v_tail_887_ = lean_ctor_get(v_x_884_, 2);
v___x_888_ = l_Lean_instBEqFVarId_beq(v_key_885_, v_a_882_);
if (v___x_888_ == 0)
{
v_x_884_ = v_tail_887_;
goto _start;
}
else
{
lean_inc(v_value_886_);
return v_value_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_890_, lean_object* v_fallback_891_, lean_object* v_x_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_890_, v_fallback_891_, v_x_892_);
lean_dec(v_x_892_);
lean_dec(v_fallback_891_);
lean_dec(v_a_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object* v_m_894_, lean_object* v_a_895_, lean_object* v_fallback_896_){
_start:
{
lean_object* v_buckets_897_; lean_object* v___x_898_; uint64_t v___x_899_; uint64_t v___x_900_; uint64_t v___x_901_; uint64_t v_fold_902_; uint64_t v___x_903_; uint64_t v___x_904_; uint64_t v___x_905_; size_t v___x_906_; size_t v___x_907_; size_t v___x_908_; size_t v___x_909_; size_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_buckets_897_ = lean_ctor_get(v_m_894_, 1);
v___x_898_ = lean_array_get_size(v_buckets_897_);
v___x_899_ = l_Lean_instHashableFVarId_hash(v_a_895_);
v___x_900_ = 32ULL;
v___x_901_ = lean_uint64_shift_right(v___x_899_, v___x_900_);
v_fold_902_ = lean_uint64_xor(v___x_899_, v___x_901_);
v___x_903_ = 16ULL;
v___x_904_ = lean_uint64_shift_right(v_fold_902_, v___x_903_);
v___x_905_ = lean_uint64_xor(v_fold_902_, v___x_904_);
v___x_906_ = lean_uint64_to_usize(v___x_905_);
v___x_907_ = lean_usize_of_nat(v___x_898_);
v___x_908_ = ((size_t)1ULL);
v___x_909_ = lean_usize_sub(v___x_907_, v___x_908_);
v___x_910_ = lean_usize_land(v___x_906_, v___x_909_);
v___x_911_ = lean_array_uget_borrowed(v_buckets_897_, v___x_910_);
v___x_912_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_895_, v_fallback_896_, v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object* v_m_913_, lean_object* v_a_914_, lean_object* v_fallback_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_913_, v_a_914_, v_fallback_915_);
lean_dec(v_fallback_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_m_913_);
return v_res_916_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_box(0);
v___x_922_ = lean_unsigned_to_nat(16u);
v___x_923_ = lean_mk_array(v___x_922_, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_924_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__1(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__0));
v___x_929_ = l_Lean_stringToMessageData(v___x_928_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__3(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__2));
v___x_932_ = l_Lean_stringToMessageData(v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__5(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__4));
v___x_935_ = l_Lean_stringToMessageData(v___x_934_);
return v___x_935_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object* v_e_936_, lean_object* v_subst_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
switch(lean_obj_tag(v_e_936_))
{
case 0:
{
lean_object* v_deBruijnIndex_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_deBruijnIndex_943_ = lean_ctor_get(v_e_936_, 0);
v___x_944_ = lean_array_get_size(v_subst_937_);
v___x_945_ = lean_nat_dec_lt(v_deBruijnIndex_943_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
lean_inc(v_deBruijnIndex_943_);
lean_dec_ref_known(v_e_936_, 1);
lean_dec_ref(v_subst_937_);
v___x_946_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__1, &l_Lean_Elab_Tactic_Do_countUses___closed__1_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__1);
v___x_947_ = l_Nat_reprFast(v_deBruijnIndex_943_);
v___x_948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
v___x_949_ = l_Lean_MessageData_ofFormat(v___x_948_);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_946_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__3, &l_Lean_Elab_Tactic_Do_countUses___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__3);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = l_Nat_reprFast(v___x_944_);
v___x_954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
v___x_955_ = l_Lean_MessageData_ofFormat(v___x_954_);
v___x_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_952_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_956_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
return v___x_957_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_958_ = lean_unsigned_to_nat(1u);
v___x_959_ = lean_nat_sub(v___x_944_, v___x_958_);
v___x_960_ = lean_nat_sub(v___x_959_, v_deBruijnIndex_943_);
lean_dec(v___x_959_);
v___x_961_ = lean_array_fget(v_subst_937_, v___x_960_);
lean_dec(v___x_960_);
lean_dec_ref(v_subst_937_);
v___x_962_ = 1;
v___x_963_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_964_ = lean_box(v___x_962_);
v___x_965_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_963_, v___x_961_, v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_e_936_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
case 1:
{
lean_object* v_fvarId_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec_ref(v_subst_937_);
v_fvarId_968_ = lean_ctor_get(v_e_936_, 0);
v___x_969_ = 1;
v___x_970_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_971_ = lean_box(v___x_969_);
lean_inc(v_fvarId_968_);
v___x_972_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_970_, v_fvarId_968_, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_e_936_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
case 5:
{
lean_object* v_fn_975_; lean_object* v_arg_976_; lean_object* v___x_977_; 
v_fn_975_ = lean_ctor_get(v_e_936_, 0);
lean_inc_ref(v_fn_975_);
v_arg_976_ = lean_ctor_get(v_e_936_, 1);
lean_inc_ref(v_arg_976_);
lean_dec_ref_known(v_e_936_, 2);
lean_inc_ref(v_subst_937_);
v___x_977_ = l_Lean_Elab_Tactic_Do_countUses(v_fn_975_, v_subst_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v_fst_979_; lean_object* v_snd_980_; lean_object* v___x_981_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v_fst_979_ = lean_ctor_get(v_a_978_, 0);
lean_inc(v_fst_979_);
v_snd_980_ = lean_ctor_get(v_a_978_, 1);
lean_inc(v_snd_980_);
lean_dec(v_a_978_);
v___x_981_ = l_Lean_Elab_Tactic_Do_countUses(v_arg_976_, v_subst_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1000_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_1000_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1000_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_fst_986_; lean_object* v_snd_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_999_; 
v_fst_986_ = lean_ctor_get(v_a_982_, 0);
v_snd_987_ = lean_ctor_get(v_a_982_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_a_982_);
if (v_isSharedCheck_999_ == 0)
{
v___x_989_ = v_a_982_;
v_isShared_990_ = v_isSharedCheck_999_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_snd_987_);
lean_inc(v_fst_986_);
lean_dec(v_a_982_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_999_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_991_ = l_Lean_Expr_app___override(v_fst_979_, v_fst_986_);
v___x_992_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_980_, v_snd_987_);
lean_dec(v_snd_980_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v___x_992_);
lean_ctor_set(v___x_989_, 0, v___x_991_);
v___x_994_ = v___x_989_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_992_);
v___x_994_ = v_reuseFailAlloc_998_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_996_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_994_);
v___x_996_ = v___x_984_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
else
{
lean_dec(v_snd_980_);
lean_dec(v_fst_979_);
return v___x_981_;
}
}
else
{
lean_dec_ref(v_arg_976_);
lean_dec_ref(v_subst_937_);
return v___x_977_;
}
}
case 6:
{
lean_object* v_binderName_1001_; lean_object* v_binderType_1002_; lean_object* v_body_1003_; uint8_t v_binderInfo_1004_; lean_object* v___x_1005_; 
v_binderName_1001_ = lean_ctor_get(v_e_936_, 0);
lean_inc(v_binderName_1001_);
v_binderType_1002_ = lean_ctor_get(v_e_936_, 1);
lean_inc_ref(v_binderType_1002_);
v_body_1003_ = lean_ctor_get(v_e_936_, 2);
lean_inc_ref(v_body_1003_);
v_binderInfo_1004_ = lean_ctor_get_uint8(v_e_936_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_936_, 3);
v___x_1005_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
lean_inc_ref(v_subst_937_);
v___x_1007_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1002_, v_subst_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v_fst_1009_; lean_object* v_snd_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v_fst_1009_ = lean_ctor_get(v_a_1008_, 0);
lean_inc(v_fst_1009_);
v_snd_1010_ = lean_ctor_get(v_a_1008_, 1);
lean_inc(v_snd_1010_);
lean_dec(v_a_1008_);
lean_inc(v_a_1006_);
v___x_1011_ = lean_array_push(v_subst_937_, v_a_1006_);
v___x_1012_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1003_, v___x_1011_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1032_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1032_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1032_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v_fst_1017_; lean_object* v_snd_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1031_; 
v_fst_1017_ = lean_ctor_get(v_a_1013_, 0);
v_snd_1018_ = lean_ctor_get(v_a_1013_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_a_1013_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1020_ = v_a_1013_;
v_isShared_1021_ = v_isSharedCheck_1031_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_snd_1018_);
lean_inc(v_fst_1017_);
lean_dec(v_a_1013_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1031_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1022_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_1010_, v_snd_1018_);
lean_dec(v_snd_1010_);
v___x_1023_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1022_, v_a_1006_);
lean_dec(v_a_1006_);
v___x_1024_ = l_Lean_Expr_lam___override(v_binderName_1001_, v_fst_1009_, v_fst_1017_, v_binderInfo_1004_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v___x_1023_);
lean_ctor_set(v___x_1020_, 0, v___x_1024_);
v___x_1026_ = v___x_1020_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v___x_1023_);
v___x_1026_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1028_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1026_);
v___x_1028_ = v___x_1015_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
else
{
lean_dec(v_snd_1010_);
lean_dec(v_fst_1009_);
lean_dec(v_a_1006_);
lean_dec(v_binderName_1001_);
return v___x_1012_;
}
}
else
{
lean_dec(v_a_1006_);
lean_dec_ref(v_body_1003_);
lean_dec(v_binderName_1001_);
lean_dec_ref(v_subst_937_);
return v___x_1007_;
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v_body_1003_);
lean_dec_ref(v_binderType_1002_);
lean_dec(v_binderName_1001_);
lean_dec_ref(v_subst_937_);
v_a_1033_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1005_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1005_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1041_; lean_object* v_binderType_1042_; lean_object* v_body_1043_; uint8_t v_binderInfo_1044_; lean_object* v___x_1045_; 
v_binderName_1041_ = lean_ctor_get(v_e_936_, 0);
lean_inc(v_binderName_1041_);
v_binderType_1042_ = lean_ctor_get(v_e_936_, 1);
lean_inc_ref(v_binderType_1042_);
v_body_1043_ = lean_ctor_get(v_e_936_, 2);
lean_inc_ref(v_body_1043_);
v_binderInfo_1044_ = lean_ctor_get_uint8(v_e_936_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_936_, 3);
v___x_1045_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
lean_inc_ref(v_subst_937_);
v___x_1047_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1042_, v_subst_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v_fst_1049_; lean_object* v_snd_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v_fst_1049_ = lean_ctor_get(v_a_1048_, 0);
lean_inc(v_fst_1049_);
v_snd_1050_ = lean_ctor_get(v_a_1048_, 1);
lean_inc(v_snd_1050_);
lean_dec(v_a_1048_);
lean_inc(v_a_1046_);
v___x_1051_ = lean_array_push(v_subst_937_, v_a_1046_);
v___x_1052_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1043_, v___x_1051_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1072_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1072_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1072_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_fst_1057_; lean_object* v_snd_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1071_; 
v_fst_1057_ = lean_ctor_get(v_a_1053_, 0);
v_snd_1058_ = lean_ctor_get(v_a_1053_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_a_1053_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1060_ = v_a_1053_;
v_isShared_1061_ = v_isSharedCheck_1071_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_snd_1058_);
lean_inc(v_fst_1057_);
lean_dec(v_a_1053_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1071_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1062_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_1050_, v_snd_1058_);
lean_dec(v_snd_1050_);
v___x_1063_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1062_, v_a_1046_);
lean_dec(v_a_1046_);
v___x_1064_ = l_Lean_Expr_forallE___override(v_binderName_1041_, v_fst_1049_, v_fst_1057_, v_binderInfo_1044_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 1, v___x_1063_);
lean_ctor_set(v___x_1060_, 0, v___x_1064_);
v___x_1066_ = v___x_1060_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1063_);
v___x_1066_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1066_);
v___x_1068_ = v___x_1055_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
else
{
lean_dec(v_snd_1050_);
lean_dec(v_fst_1049_);
lean_dec(v_a_1046_);
lean_dec(v_binderName_1041_);
return v___x_1052_;
}
}
else
{
lean_dec(v_a_1046_);
lean_dec_ref(v_body_1043_);
lean_dec(v_binderName_1041_);
lean_dec_ref(v_subst_937_);
return v___x_1047_;
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v_body_1043_);
lean_dec_ref(v_binderType_1042_);
lean_dec(v_binderName_1041_);
lean_dec_ref(v_subst_937_);
v_a_1073_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1045_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1045_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
case 8:
{
lean_object* v_declName_1081_; lean_object* v_type_1082_; lean_object* v_value_1083_; lean_object* v_body_1084_; uint8_t v_nondep_1085_; lean_object* v___x_1086_; 
v_declName_1081_ = lean_ctor_get(v_e_936_, 0);
lean_inc(v_declName_1081_);
v_type_1082_ = lean_ctor_get(v_e_936_, 1);
lean_inc_ref(v_type_1082_);
v_value_1083_ = lean_ctor_get(v_e_936_, 2);
lean_inc_ref(v_value_1083_);
v_body_1084_ = lean_ctor_get(v_e_936_, 3);
lean_inc_ref(v_body_1084_);
v_nondep_1085_ = lean_ctor_get_uint8(v_e_936_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_936_, 4);
v___x_1086_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc_n(v_a_1087_, 2);
lean_dec_ref_known(v___x_1086_, 1);
lean_inc_ref(v_subst_937_);
v___x_1088_ = lean_array_push(v_subst_937_, v_a_1087_);
v___x_1089_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1084_, v___x_1088_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1132_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1132_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1132_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___x_1097_; 
v_fst_1094_ = lean_ctor_get(v_a_1090_, 0);
lean_inc(v_fst_1094_);
v_snd_1095_ = lean_ctor_get(v_a_1090_, 1);
lean_inc(v_snd_1095_);
lean_dec(v_a_1090_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 1);
lean_ctor_set(v___x_1092_, 0, v_value_1083_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_value_1083_);
v___x_1097_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_a_1087_, v_type_1082_, v___x_1097_, v_snd_1095_, v_subst_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_1087_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1122_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1122_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1122_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_snd_1103_; lean_object* v_fst_1104_; 
v_snd_1103_ = lean_ctor_get(v_a_1099_, 1);
lean_inc(v_snd_1103_);
v_fst_1104_ = lean_ctor_get(v_snd_1103_, 0);
lean_inc(v_fst_1104_);
if (lean_obj_tag(v_fst_1104_) == 1)
{
lean_object* v_fst_1105_; lean_object* v_snd_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1118_; 
v_fst_1105_ = lean_ctor_get(v_a_1099_, 0);
lean_inc(v_fst_1105_);
lean_dec(v_a_1099_);
v_snd_1106_ = lean_ctor_get(v_snd_1103_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_snd_1103_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; 
v_unused_1119_ = lean_ctor_get(v_snd_1103_, 0);
lean_dec(v_unused_1119_);
v___x_1108_ = v_snd_1103_;
v_isShared_1109_ = v_isSharedCheck_1118_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_snd_1106_);
lean_dec(v_snd_1103_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1118_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_val_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v_val_1110_ = lean_ctor_get(v_fst_1104_, 0);
lean_inc(v_val_1110_);
lean_dec_ref_known(v_fst_1104_, 1);
v___x_1111_ = l_Lean_Expr_letE___override(v_declName_1081_, v_fst_1105_, v_val_1110_, v_fst_1094_, v_nondep_1085_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_snd_1106_);
v___x_1113_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1115_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1113_);
v___x_1115_ = v___x_1101_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v_fst_1104_);
lean_dec(v_snd_1103_);
lean_del_object(v___x_1101_);
lean_dec(v_a_1099_);
lean_dec(v_fst_1094_);
lean_dec(v_declName_1081_);
v___x_1120_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
v___x_1121_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_1120_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
return v___x_1121_;
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v_fst_1094_);
lean_dec(v_declName_1081_);
v_a_1123_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1098_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1098_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1087_);
lean_dec_ref(v_value_1083_);
lean_dec_ref(v_type_1082_);
lean_dec(v_declName_1081_);
lean_dec_ref(v_subst_937_);
return v___x_1089_;
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_body_1084_);
lean_dec_ref(v_value_1083_);
lean_dec_ref(v_type_1082_);
lean_dec(v_declName_1081_);
lean_dec_ref(v_subst_937_);
v_a_1133_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1086_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1086_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
case 10:
{
lean_object* v_data_1141_; lean_object* v_expr_1142_; lean_object* v___f_1143_; lean_object* v___x_1144_; 
v_data_1141_ = lean_ctor_get(v_e_936_, 0);
lean_inc(v_data_1141_);
v_expr_1142_ = lean_ctor_get(v_e_936_, 1);
lean_inc_ref(v_expr_1142_);
lean_dec_ref_known(v_e_936_, 2);
v___f_1143_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__0), 2, 1);
lean_closure_set(v___f_1143_, 0, v_data_1141_);
v___x_1144_ = l_Lean_Elab_Tactic_Do_countUses(v_expr_1142_, v_subst_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1153_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1143_, v_a_1145_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1149_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_dec_ref(v___f_1143_);
return v___x_1144_;
}
}
case 11:
{
lean_object* v_typeName_1154_; lean_object* v_idx_1155_; lean_object* v_struct_1156_; lean_object* v___f_1157_; lean_object* v___x_1158_; 
v_typeName_1154_ = lean_ctor_get(v_e_936_, 0);
lean_inc(v_typeName_1154_);
v_idx_1155_ = lean_ctor_get(v_e_936_, 1);
lean_inc(v_idx_1155_);
v_struct_1156_ = lean_ctor_get(v_e_936_, 2);
lean_inc_ref(v_struct_1156_);
lean_dec_ref_known(v_e_936_, 3);
v___f_1157_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__1), 3, 2);
lean_closure_set(v___f_1157_, 0, v_typeName_1154_);
lean_closure_set(v___f_1157_, 1, v_idx_1155_);
v___x_1158_ = l_Lean_Elab_Tactic_Do_countUses(v_struct_1156_, v_subst_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1167_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1163_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1157_, v_a_1159_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1163_);
v___x_1165_ = v___x_1161_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
else
{
lean_dec_ref(v___f_1157_);
return v___x_1158_;
}
}
default: 
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec_ref(v_subst_937_);
v___x_1168_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_e_936_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_countUses_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_936_ = stack[0].m_obj;
lean_object* v_subst_937_ = stack[1].m_obj;
lean_object* v_a_938_ = stack[2].m_obj;
lean_object* v_a_939_ = stack[3].m_obj;
lean_object* v_a_940_ = stack[4].m_obj;
lean_object* v_a_941_ = stack[5].m_obj;
lean_object* v_res_1171_;
v_res_1171_ = l_Lean_Elab_Tactic_Do_countUses(v_e_936_, v_subst_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
stack->m_obj
 = v_res_1171_;
}
lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object* v_fvarId_1172_, lean_object* v_ty_1173_, lean_object* v_val_x3f_1174_, lean_object* v_bodyUses_1175_, lean_object* v_subst_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___f_1182_; lean_object* v___x_1183_; 
v___f_1182_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0));
lean_inc_ref(v_subst_1176_);
v___x_1183_ = l_Lean_Elab_Tactic_Do_countUses(v_ty_1173_, v_subst_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1238_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1238_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1238_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_fst_1188_; lean_object* v_snd_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1237_; 
v_fst_1188_ = lean_ctor_get(v_a_1184_, 0);
v_snd_1189_ = lean_ctor_get(v_a_1184_, 1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_a_1184_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1191_ = v_a_1184_;
v_isShared_1192_ = v_isSharedCheck_1237_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_snd_1189_);
lean_inc(v_fst_1188_);
lean_dec(v_a_1184_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1237_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
uint8_t v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v_fst_1211_; lean_object* v_snd_1212_; 
if (lean_obj_tag(v_val_x3f_1174_) == 0)
{
lean_object* v___x_1222_; 
lean_dec_ref(v_subst_1176_);
v___x_1222_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v_fst_1211_ = v_val_x3f_1174_;
v_snd_1212_ = v___x_1222_;
goto v___jp_1210_;
}
else
{
lean_object* v_val_1223_; lean_object* v___x_1224_; 
v_val_1223_ = lean_ctor_get(v_val_x3f_1174_, 0);
lean_inc(v_val_1223_);
lean_dec_ref_known(v_val_x3f_1174_, 1);
v___x_1224_ = l_Lean_Elab_Tactic_Do_countUses(v_val_1223_, v_subst_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1226_; lean_object* v_fst_1227_; lean_object* v_snd_1228_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v___x_1226_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1182_, v_a_1225_);
v_fst_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_fst_1227_);
v_snd_1228_ = lean_ctor_get(v___x_1226_, 1);
lean_inc(v_snd_1228_);
lean_dec_ref(v___x_1226_);
v_fst_1211_ = v_fst_1227_;
v_snd_1212_ = v_snd_1228_;
goto v___jp_1210_;
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_del_object(v___x_1191_);
lean_dec(v_snd_1189_);
lean_dec(v_fst_1188_);
lean_del_object(v___x_1186_);
lean_dec_ref(v_bodyUses_1175_);
v_a_1229_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1224_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1224_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
v___jp_1193_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1197_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_1196_, v_fvarId_1172_);
v___x_1198_ = lean_box(0);
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_1200_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1194_);
v___x_1201_ = l_Lean_KVMap_setNat(v___x_1198_, v___x_1199_, v___x_1200_);
v___x_1202_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1201_, v_fst_1188_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 1, v___x_1197_);
lean_ctor_set(v___x_1191_, 0, v___y_1195_);
v___x_1204_ = v___x_1191_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___y_1195_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1197_);
v___x_1204_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1202_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1205_);
v___x_1207_ = v___x_1186_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
v___jp_1210_:
{
uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; uint8_t v___x_1217_; 
v___x_1213_ = 0;
v___x_1214_ = lean_box(v___x_1213_);
v___x_1215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_1175_, v_fvarId_1172_, v___x_1214_);
lean_dec(v___x_1214_);
v___x_1216_ = lean_unbox(v___x_1215_);
v___x_1217_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_1216_, v___x_1213_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1218_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_1175_, v_snd_1189_);
lean_dec_ref(v_bodyUses_1175_);
v___x_1219_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_1218_, v_snd_1212_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = lean_unbox(v___x_1215_);
lean_dec(v___x_1215_);
v___y_1194_ = v___x_1220_;
v___y_1195_ = v_fst_1211_;
v___y_1196_ = v___x_1219_;
goto v___jp_1193_;
}
else
{
uint8_t v___x_1221_; 
lean_dec_ref(v_snd_1212_);
lean_dec(v_snd_1189_);
v___x_1221_ = lean_unbox(v___x_1215_);
lean_dec(v___x_1215_);
v___y_1194_ = v___x_1221_;
v___y_1195_ = v_fst_1211_;
v___y_1196_ = v_bodyUses_1175_;
goto v___jp_1193_;
}
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v_subst_1176_);
lean_dec_ref(v_bodyUses_1175_);
lean_dec(v_val_x3f_1174_);
v_a_1239_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1183_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1183_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_countUsesDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1172_ = stack[0].m_obj;
lean_object* v_ty_1173_ = stack[1].m_obj;
lean_object* v_val_x3f_1174_ = stack[2].m_obj;
lean_object* v_bodyUses_1175_ = stack[3].m_obj;
lean_object* v_subst_1176_ = stack[4].m_obj;
lean_object* v_a_1177_ = stack[5].m_obj;
lean_object* v_a_1178_ = stack[6].m_obj;
lean_object* v_a_1179_ = stack[7].m_obj;
lean_object* v_a_1180_ = stack[8].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1172_, v_ty_1173_, v_val_x3f_1174_, v_bodyUses_1175_, v_subst_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object* v_fvarId_1248_, lean_object* v_ty_1249_, lean_object* v_val_x3f_1250_, lean_object* v_bodyUses_1251_, lean_object* v_subst_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1248_, v_ty_1249_, v_val_x3f_1250_, v_bodyUses_1251_, v_subst_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_fvarId_1248_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object* v_e_1259_, lean_object* v_subst_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Elab_Tactic_Do_countUses(v_e_1259_, v_subst_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object* v_00_u03b2_1267_, lean_object* v_m_1268_, lean_object* v_a_1269_, lean_object* v_fallback_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_1268_, v_a_1269_, v_fallback_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object* v_00_u03b2_1272_, lean_object* v_m_1273_, lean_object* v_a_1274_, lean_object* v_fallback_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_1272_, v_m_1273_, v_a_1274_, v_fallback_1275_);
lean_dec(v_fallback_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_m_1273_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object* v_00_u03b2_1277_, lean_object* v_m_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_1278_, v_a_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object* v_00_u03b2_1281_, lean_object* v_m_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(v_00_u03b2_1281_, v_m_1282_, v_a_1283_);
lean_dec(v_a_1283_);
return v_res_1284_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object* v_00_u03b1_1285_, lean_object* v_msg_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1286_ = stack[1].m_obj;
lean_object* v___y_1287_ = stack[2].m_obj;
lean_object* v___y_1288_ = stack[3].m_obj;
lean_object* v___y_1289_ = stack[4].m_obj;
lean_object* v___y_1290_ = stack[5].m_obj;
lean_object* v_res_1293_;
v_res_1293_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_box(0), v_msg_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
stack->m_obj
 = v_res_1293_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object* v_00_u03b1_1294_, lean_object* v_msg_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(v_00_u03b1_1294_, v_msg_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object* v_00_u03b2_1302_, lean_object* v_m_1303_, lean_object* v_a_1304_, lean_object* v_b_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_1303_, v_a_1304_, v_b_1305_);
return v___x_1306_;
}
}
lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT void l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1307_ = stack[0].m_obj;
lean_object* v___y_1308_ = stack[1].m_obj;
lean_object* v___y_1309_ = stack[2].m_obj;
lean_object* v___y_1310_ = stack[3].m_obj;
lean_object* v_res_1313_;
v_res_1313_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
stack->m_obj
 = v_res_1313_;
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object* v_00_u03b2_1320_, lean_object* v_a_1321_, lean_object* v_fallback_1322_, lean_object* v_x_1323_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_1321_, v_fallback_1322_, v_x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1325_, lean_object* v_a_1326_, lean_object* v_fallback_1327_, lean_object* v_x_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_1325_, v_a_1326_, v_fallback_1327_, v_x_1328_);
lean_dec(v_x_1328_);
lean_dec(v_fallback_1327_);
lean_dec(v_a_1326_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object* v_00_u03b2_1330_, lean_object* v_a_1331_, lean_object* v_x_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_1331_, v_x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1334_, lean_object* v_a_1335_, lean_object* v_x_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_1334_, v_a_1335_, v_x_1336_);
lean_dec(v_a_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object* v_00_u03b2_1338_, lean_object* v_a_1339_, lean_object* v_b_1340_, lean_object* v_x_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_1339_, v_b_1340_, v_x_1341_);
return v___x_1342_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object* v_as_1345_, size_t v_i_1346_, size_t v_stop_1347_, lean_object* v_b_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_usize_dec_eq(v_i_1346_, v_stop_1347_);
if (v___x_1354_ == 0)
{
size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = ((size_t)1ULL);
v___x_1356_ = lean_usize_sub(v_i_1346_, v___x_1355_);
v___x_1357_ = lean_array_uget_borrowed(v_as_1345_, v___x_1356_);
if (lean_obj_tag(v___x_1357_) == 0)
{
v_i_1346_ = v___x_1356_;
goto _start;
}
else
{
lean_object* v_val_1359_; lean_object* v_fst_1360_; lean_object* v_snd_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v_val_1359_ = lean_ctor_get(v___x_1357_, 0);
v_fst_1360_ = lean_ctor_get(v_b_1348_, 0);
lean_inc(v_fst_1360_);
v_snd_1361_ = lean_ctor_get(v_b_1348_, 1);
lean_inc(v_snd_1361_);
lean_dec_ref(v_b_1348_);
v___x_1362_ = l_Lean_LocalDecl_fvarId(v_val_1359_);
v___x_1363_ = l_Lean_LocalDecl_type(v_val_1359_);
v___x_1364_ = l_Lean_LocalDecl_value_x3f(v_val_1359_, v___x_1354_);
v___x_1365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_1366_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v___x_1362_, v___x_1363_, v___x_1364_, v_snd_1361_, v___x_1365_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___x_1362_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v_snd_1368_; lean_object* v_fst_1369_; lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1386_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v_snd_1368_ = lean_ctor_get(v_a_1367_, 1);
lean_inc(v_snd_1368_);
v_fst_1369_ = lean_ctor_get(v_a_1367_, 0);
lean_inc(v_fst_1369_);
lean_dec(v_a_1367_);
v_fst_1370_ = lean_ctor_get(v_snd_1368_, 0);
v_snd_1371_ = lean_ctor_get(v_snd_1368_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_snd_1368_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1373_ = v_snd_1368_;
v_isShared_1374_ = v_isSharedCheck_1386_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snd_1371_);
lean_inc(v_fst_1370_);
lean_dec(v_snd_1368_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1386_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___y_1376_; 
if (lean_obj_tag(v_fst_1370_) == 0)
{
lean_object* v___x_1382_; 
lean_inc(v_val_1359_);
v___x_1382_ = l_Lean_LocalDecl_setType(v_val_1359_, v_fst_1369_);
v___y_1376_ = v___x_1382_;
goto v___jp_1375_;
}
else
{
lean_object* v_val_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_val_1383_ = lean_ctor_get(v_fst_1370_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_fst_1370_, 1);
lean_inc(v_val_1359_);
v___x_1384_ = l_Lean_LocalDecl_setType(v_val_1359_, v_fst_1369_);
v___x_1385_ = l_Lean_LocalDecl_setValue(v___x_1384_, v_val_1383_);
v___y_1376_ = v___x_1385_;
goto v___jp_1375_;
}
v___jp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = lean_array_push(v_fst_1360_, v___y_1376_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1377_);
v___x_1379_ = v___x_1373_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_snd_1371_);
v___x_1379_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
v_i_1346_ = v___x_1356_;
v_b_1348_ = v___x_1379_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_fst_1360_);
v_a_1387_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1366_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1366_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_b_1348_);
return v___x_1395_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1345_ = stack[0].m_obj;
size_t v_i_1346_ = stack[1].m_num;
size_t v_stop_1347_ = stack[2].m_num;
lean_object* v_b_1348_ = stack[3].m_obj;
lean_object* v___y_1349_ = stack[4].m_obj;
lean_object* v___y_1350_ = stack[5].m_obj;
lean_object* v___y_1351_ = stack[6].m_obj;
lean_object* v___y_1352_ = stack[7].m_obj;
lean_object* v_res_1396_;
v_res_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1345_, v_i_1346_, v_stop_1347_, v_b_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
stack->m_obj
 = v_res_1396_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1397_, lean_object* v_i_1398_, lean_object* v_stop_1399_, lean_object* v_b_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
size_t v_i_boxed_1406_; size_t v_stop_boxed_1407_; lean_object* v_res_1408_; 
v_i_boxed_1406_ = lean_unbox_usize(v_i_1398_);
lean_dec(v_i_1398_);
v_stop_boxed_1407_ = lean_unbox_usize(v_stop_1399_);
lean_dec(v_stop_1399_);
v_res_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1397_, v_i_boxed_1406_, v_stop_boxed_1407_, v_b_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec_ref(v_as_1397_);
return v_res_1408_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object* v_x_1409_, lean_object* v_x_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
if (lean_obj_tag(v_x_1409_) == 0)
{
lean_object* v_cs_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1429_; 
v_cs_1416_ = lean_ctor_get(v_x_1409_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_x_1409_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1418_ = v_x_1409_;
v_isShared_1419_ = v_isSharedCheck_1429_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_cs_1416_);
lean_dec(v_x_1409_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1429_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = lean_array_get_size(v_cs_1416_);
v___x_1421_ = lean_unsigned_to_nat(0u);
v___x_1422_ = lean_nat_dec_lt(v___x_1421_, v___x_1420_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1424_; 
lean_dec_ref(v_cs_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v_x_1410_);
v___x_1424_ = v___x_1418_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_x_1410_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
else
{
size_t v___x_1426_; size_t v___x_1427_; lean_object* v___x_1428_; 
lean_del_object(v___x_1418_);
v___x_1426_ = lean_usize_of_nat(v___x_1420_);
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_1416_, v___x_1426_, v___x_1427_, v_x_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec_ref(v_cs_1416_);
return v___x_1428_;
}
}
}
else
{
lean_object* v_vs_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1443_; 
v_vs_1430_ = lean_ctor_get(v_x_1409_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_x_1409_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1432_ = v_x_1409_;
v_isShared_1433_ = v_isSharedCheck_1443_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_vs_1430_);
lean_dec(v_x_1409_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1443_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = lean_array_get_size(v_vs_1430_);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_nat_dec_lt(v___x_1435_, v___x_1434_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1438_; 
lean_dec_ref(v_vs_1430_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set_tag(v___x_1432_, 0);
lean_ctor_set(v___x_1432_, 0, v_x_1410_);
v___x_1438_ = v___x_1432_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_x_1410_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
else
{
size_t v___x_1440_; size_t v___x_1441_; lean_object* v___x_1442_; 
lean_del_object(v___x_1432_);
v___x_1440_ = lean_usize_of_nat(v___x_1434_);
v___x_1441_ = ((size_t)0ULL);
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_1430_, v___x_1440_, v___x_1441_, v_x_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec_ref(v_vs_1430_);
return v___x_1442_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1409_ = stack[0].m_obj;
lean_object* v_x_1410_ = stack[1].m_obj;
lean_object* v___y_1411_ = stack[2].m_obj;
lean_object* v___y_1412_ = stack[3].m_obj;
lean_object* v___y_1413_ = stack[4].m_obj;
lean_object* v___y_1414_ = stack[5].m_obj;
lean_object* v_res_1444_;
v_res_1444_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1409_, v_x_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
stack->m_obj
 = v_res_1444_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_1445_, size_t v_i_1446_, size_t v_stop_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_usize_dec_eq(v_i_1446_, v_stop_1447_);
if (v___x_1454_ == 0)
{
size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1455_ = ((size_t)1ULL);
v___x_1456_ = lean_usize_sub(v_i_1446_, v___x_1455_);
v___x_1457_ = lean_array_uget_borrowed(v_as_1445_, v___x_1456_);
lean_inc(v___x_1457_);
v___x_1458_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_1457_, v_b_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
v_i_1446_ = v___x_1456_;
v_b_1448_ = v_a_1459_;
goto _start;
}
else
{
return v___x_1458_;
}
}
else
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_b_1448_);
return v___x_1461_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1445_ = stack[0].m_obj;
size_t v_i_1446_ = stack[1].m_num;
size_t v_stop_1447_ = stack[2].m_num;
lean_object* v_b_1448_ = stack[3].m_obj;
lean_object* v___y_1449_ = stack[4].m_obj;
lean_object* v___y_1450_ = stack[5].m_obj;
lean_object* v___y_1451_ = stack[6].m_obj;
lean_object* v___y_1452_ = stack[7].m_obj;
lean_object* v_res_1462_;
v_res_1462_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1445_, v_i_1446_, v_stop_1447_, v_b_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
stack->m_obj
 = v_res_1462_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1463_, lean_object* v_i_1464_, lean_object* v_stop_1465_, lean_object* v_b_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
size_t v_i_boxed_1472_; size_t v_stop_boxed_1473_; lean_object* v_res_1474_; 
v_i_boxed_1472_ = lean_unbox_usize(v_i_1464_);
lean_dec(v_i_1464_);
v_stop_boxed_1473_ = lean_unbox_usize(v_stop_1465_);
lean_dec(v_stop_1465_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1463_, v_i_boxed_1472_, v_stop_boxed_1473_, v_b_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec_ref(v_as_1463_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1475_, lean_object* v_x_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1475_, v_x_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1482_;
}
}
lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object* v_t_1483_, lean_object* v_init_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_root_1490_; lean_object* v_tail_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v_root_1490_ = lean_ctor_get(v_t_1483_, 0);
lean_inc_ref(v_root_1490_);
v_tail_1491_ = lean_ctor_get(v_t_1483_, 1);
lean_inc_ref(v_tail_1491_);
lean_dec_ref(v_t_1483_);
v___x_1492_ = lean_array_get_size(v_tail_1491_);
v___x_1493_ = lean_unsigned_to_nat(0u);
v___x_1494_ = lean_nat_dec_lt(v___x_1493_, v___x_1492_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec_ref(v_tail_1491_);
v___x_1495_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1490_, v_init_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1495_;
}
else
{
size_t v___x_1496_; size_t v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = lean_usize_of_nat(v___x_1492_);
v___x_1497_ = ((size_t)0ULL);
v___x_1498_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_1491_, v___x_1496_, v___x_1497_, v_init_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec_ref(v_tail_1491_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1500_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1498_, 1);
v___x_1500_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1490_, v_a_1499_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1500_;
}
else
{
lean_dec_ref(v_root_1490_);
return v___x_1498_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1483_ = stack[0].m_obj;
lean_object* v_init_1484_ = stack[1].m_obj;
lean_object* v___y_1485_ = stack[2].m_obj;
lean_object* v___y_1486_ = stack[3].m_obj;
lean_object* v___y_1487_ = stack[4].m_obj;
lean_object* v___y_1488_ = stack[5].m_obj;
lean_object* v_res_1501_;
v_res_1501_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1483_, v_init_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
stack->m_obj
 = v_res_1501_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object* v_t_1502_, lean_object* v_init_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1502_, v_init_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1509_;
}
}
lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object* v_lctx_1510_, lean_object* v_init_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_decls_1517_; lean_object* v___x_1518_; 
v_decls_1517_ = lean_ctor_get(v_lctx_1510_, 1);
lean_inc_ref(v_decls_1517_);
lean_dec_ref(v_lctx_1510_);
v___x_1518_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_1517_, v_init_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1518_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1510_ = stack[0].m_obj;
lean_object* v_init_1511_ = stack[1].m_obj;
lean_object* v___y_1512_ = stack[2].m_obj;
lean_object* v___y_1513_ = stack[3].m_obj;
lean_object* v___y_1514_ = stack[4].m_obj;
lean_object* v___y_1515_ = stack[5].m_obj;
lean_object* v_res_1519_;
v_res_1519_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1510_, v_init_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
stack->m_obj
 = v_res_1519_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object* v_lctx_1520_, lean_object* v_init_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1520_, v_init_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1527_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t v_sz_1528_, size_t v_i_1529_, lean_object* v_bs_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_usize_dec_lt(v_i_1529_, v_sz_1528_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_bs_1530_);
return v___x_1534_;
}
else
{
lean_object* v_v_1535_; lean_object* v___x_1536_; lean_object* v_bs_x27_1537_; lean_object* v_a_1539_; 
v_v_1535_ = lean_array_uget(v_bs_1530_, v_i_1529_);
v___x_1536_ = lean_unsigned_to_nat(0u);
v_bs_x27_1537_ = lean_array_uset(v_bs_1530_, v_i_1529_, v___x_1536_);
if (lean_obj_tag(v_v_1535_) == 0)
{
v_a_1539_ = v_v_1535_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1558_; 
v_isSharedCheck_1558_ = !lean_is_exclusive(v_v_1535_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v_v_1535_, 0);
lean_dec(v_unused_1559_);
v___x_1545_ = v_v_1535_;
v_isShared_1546_ = v_isSharedCheck_1558_;
goto v_resetjp_1544_;
}
else
{
lean_dec(v_v_1535_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1558_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1547_ = l_Lean_instInhabitedLocalDecl_default;
v___x_1548_ = lean_st_ref_take(v___y_1531_);
v___x_1549_ = lean_array_get_size(v___x_1548_);
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_sub(v___x_1549_, v___x_1550_);
v___x_1552_ = lean_array_get_borrowed(v___x_1547_, v___x_1548_, v___x_1551_);
lean_dec(v___x_1551_);
lean_inc(v___x_1552_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1552_);
v___x_1554_ = v___x_1545_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_array_pop(v___x_1548_);
v___x_1556_ = lean_st_ref_put(v___y_1531_, v___x_1555_);
v_a_1539_ = v___x_1554_;
goto v___jp_1538_;
}
}
}
v___jp_1538_:
{
size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = ((size_t)1ULL);
v___x_1541_ = lean_usize_add(v_i_1529_, v___x_1540_);
v___x_1542_ = lean_array_uset(v_bs_x27_1537_, v_i_1529_, v_a_1539_);
v_i_1529_ = v___x_1541_;
v_bs_1530_ = v___x_1542_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1528_ = stack[0].m_num;
size_t v_i_1529_ = stack[1].m_num;
lean_object* v_bs_1530_ = stack[2].m_obj;
lean_object* v___y_1531_ = stack[3].m_obj;
lean_object* v_res_1560_;
v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1528_, v_i_1529_, v_bs_1530_, v___y_1531_);
stack->m_obj
 = v_res_1560_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object* v_sz_1561_, lean_object* v_i_1562_, lean_object* v_bs_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
size_t v_sz_boxed_1566_; size_t v_i_boxed_1567_; lean_object* v_res_1568_; 
v_sz_boxed_1566_ = lean_unbox_usize(v_sz_1561_);
lean_dec(v_sz_1561_);
v_i_boxed_1567_ = lean_unbox_usize(v_i_1562_);
lean_dec(v_i_1562_);
v_res_1568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_1566_, v_i_boxed_1567_, v_bs_1563_, v___y_1564_);
lean_dec(v___y_1564_);
return v_res_1568_;
}
}
lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object* v_x_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
if (lean_obj_tag(v_x_1569_) == 0)
{
lean_object* v_cs_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1602_; 
v_cs_1576_ = lean_ctor_get(v_x_1569_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_x_1569_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1578_ = v_x_1569_;
v_isShared_1579_ = v_isSharedCheck_1602_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_cs_1576_);
lean_dec(v_x_1569_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1602_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
size_t v_sz_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
v_sz_1580_ = lean_array_size(v_cs_1576_);
v___x_1581_ = ((size_t)0ULL);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1580_, v___x_1581_, v_cs_1576_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1593_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1593_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v_a_1583_);
v___x_1588_ = v___x_1578_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1590_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1588_);
v___x_1590_ = v___x_1585_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_del_object(v___x_1578_);
v_a_1594_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1582_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1582_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
else
{
lean_object* v_vs_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1629_; 
v_vs_1603_ = lean_ctor_get(v_x_1569_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_x_1569_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1605_ = v_x_1569_;
v_isShared_1606_ = v_isSharedCheck_1629_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_vs_1603_);
lean_dec(v_x_1569_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1629_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
size_t v_sz_1607_; size_t v___x_1608_; lean_object* v___x_1609_; 
v_sz_1607_ = lean_array_size(v_vs_1603_);
v___x_1608_ = ((size_t)0ULL);
v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1607_, v___x_1608_, v_vs_1603_, v___y_1570_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1620_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1620_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1620_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v_a_1610_);
v___x_1615_ = v___x_1605_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1617_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1615_);
v___x_1617_ = v___x_1612_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_del_object(v___x_1605_);
v_a_1621_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1609_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1609_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1569_ = stack[0].m_obj;
lean_object* v___y_1570_ = stack[1].m_obj;
lean_object* v___y_1571_ = stack[2].m_obj;
lean_object* v___y_1572_ = stack[3].m_obj;
lean_object* v___y_1573_ = stack[4].m_obj;
lean_object* v___y_1574_ = stack[5].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
stack->m_obj
 = v_res_1630_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t v_sz_1631_, size_t v_i_1632_, lean_object* v_bs_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
uint8_t v___x_1640_; 
v___x_1640_ = lean_usize_dec_lt(v_i_1632_, v_sz_1631_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; 
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v_bs_1633_);
return v___x_1641_;
}
else
{
lean_object* v_v_1642_; lean_object* v___x_1643_; lean_object* v_bs_x27_1644_; lean_object* v___x_1645_; 
v_v_1642_ = lean_array_uget(v_bs_1633_, v_i_1632_);
v___x_1643_ = lean_unsigned_to_nat(0u);
v_bs_x27_1644_ = lean_array_uset(v_bs_1633_, v_i_1632_, v___x_1643_);
v___x_1645_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_1642_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; size_t v___x_1647_; size_t v___x_1648_; lean_object* v___x_1649_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = ((size_t)1ULL);
v___x_1648_ = lean_usize_add(v_i_1632_, v___x_1647_);
v___x_1649_ = lean_array_uset(v_bs_x27_1644_, v_i_1632_, v_a_1646_);
v_i_1632_ = v___x_1648_;
v_bs_1633_ = v___x_1649_;
goto _start;
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v_bs_x27_1644_);
v_a_1651_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1645_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1645_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1631_ = stack[0].m_num;
size_t v_i_1632_ = stack[1].m_num;
lean_object* v_bs_1633_ = stack[2].m_obj;
lean_object* v___y_1634_ = stack[3].m_obj;
lean_object* v___y_1635_ = stack[4].m_obj;
lean_object* v___y_1636_ = stack[5].m_obj;
lean_object* v___y_1637_ = stack[6].m_obj;
lean_object* v___y_1638_ = stack[7].m_obj;
lean_object* v_res_1659_;
v_res_1659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1631_, v_i_1632_, v_bs_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
stack->m_obj
 = v_res_1659_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_1660_, lean_object* v_i_1661_, lean_object* v_bs_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
size_t v_sz_boxed_1669_; size_t v_i_boxed_1670_; lean_object* v_res_1671_; 
v_sz_boxed_1669_ = lean_unbox_usize(v_sz_1660_);
lean_dec(v_sz_1660_);
v_i_boxed_1670_ = lean_unbox_usize(v_i_1661_);
lean_dec(v_i_1661_);
v_res_1671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_1669_, v_i_boxed_1670_, v_bs_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object* v_x_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
return v_res_1679_;
}
}
lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object* v_t_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_root_1687_; lean_object* v_tail_1688_; lean_object* v_size_1689_; size_t v_shift_1690_; lean_object* v_tailOff_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1727_; 
v_root_1687_ = lean_ctor_get(v_t_1680_, 0);
v_tail_1688_ = lean_ctor_get(v_t_1680_, 1);
v_size_1689_ = lean_ctor_get(v_t_1680_, 2);
v_shift_1690_ = lean_ctor_get_usize(v_t_1680_, 4);
v_tailOff_1691_ = lean_ctor_get(v_t_1680_, 3);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_t_1680_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1693_ = v_t_1680_;
v_isShared_1694_ = v_isSharedCheck_1727_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_tailOff_1691_);
lean_inc(v_size_1689_);
lean_inc(v_tail_1688_);
lean_inc(v_root_1687_);
lean_dec(v_t_1680_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1727_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_1687_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; size_t v_sz_1697_; size_t v___x_1698_; lean_object* v___x_1699_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
v_sz_1697_ = lean_array_size(v_tail_1688_);
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1697_, v___x_1698_, v_tail_1688_, v___y_1681_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1710_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1710_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1710_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 1, v_a_1700_);
lean_ctor_set(v___x_1693_, 0, v_a_1696_);
v___x_1705_ = v___x_1693_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1696_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_a_1700_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_size_1689_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_tailOff_1691_);
lean_ctor_set_usize(v_reuseFailAlloc_1709_, 4, v_shift_1690_);
v___x_1705_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1707_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1705_);
v___x_1707_ = v___x_1702_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v_a_1696_);
lean_del_object(v___x_1693_);
lean_dec(v_tailOff_1691_);
lean_dec(v_size_1689_);
v_a_1711_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1699_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1699_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_del_object(v___x_1693_);
lean_dec(v_tailOff_1691_);
lean_dec(v_size_1689_);
lean_dec_ref(v_tail_1688_);
v_a_1719_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1695_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1695_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1680_ = stack[0].m_obj;
lean_object* v___y_1681_ = stack[1].m_obj;
lean_object* v___y_1682_ = stack[2].m_obj;
lean_object* v___y_1683_ = stack[3].m_obj;
lean_object* v___y_1684_ = stack[4].m_obj;
lean_object* v___y_1685_ = stack[5].m_obj;
lean_object* v_res_1728_;
v_res_1728_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
stack->m_obj
 = v_res_1728_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object* v_t_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
return v_res_1736_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object* v_ctx_1737_, lean_object* v_targetUses_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_decls_1744_; lean_object* v_fvarIdToDecl_1745_; lean_object* v_auxDeclToFullName_1746_; lean_object* v_size_1747_; lean_object* v_decls_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_decls_1744_ = lean_ctor_get(v_ctx_1737_, 1);
lean_inc_ref(v_decls_1744_);
v_fvarIdToDecl_1745_ = lean_ctor_get(v_ctx_1737_, 0);
lean_inc_ref(v_fvarIdToDecl_1745_);
v_auxDeclToFullName_1746_ = lean_ctor_get(v_ctx_1737_, 2);
lean_inc(v_auxDeclToFullName_1746_);
v_size_1747_ = lean_ctor_get(v_decls_1744_, 2);
v_decls_1748_ = lean_mk_empty_array_with_capacity(v_size_1747_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_decls_1748_);
lean_ctor_set(v___x_1749_, 1, v_targetUses_1738_);
v___x_1750_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_ctx_1737_, v___x_1749_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v_fst_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v_fst_1752_ = lean_ctor_get(v_a_1751_, 0);
lean_inc(v_fst_1752_);
lean_dec(v_a_1751_);
v___x_1753_ = lean_st_mk_ref(v_fst_1752_);
v___x_1754_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_1744_, v___x_1753_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1764_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1764_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1764_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1759_ = lean_st_ref_get(v___x_1753_);
lean_dec(v___x_1753_);
lean_dec(v___x_1759_);
v___x_1760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1760_, 0, v_fvarIdToDecl_1745_);
lean_ctor_set(v___x_1760_, 1, v_a_1755_);
lean_ctor_set(v___x_1760_, 2, v_auxDeclToFullName_1746_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1760_);
v___x_1762_ = v___x_1757_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v___x_1753_);
lean_dec(v_auxDeclToFullName_1746_);
lean_dec_ref(v_fvarIdToDecl_1745_);
v_a_1765_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1754_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1754_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_auxDeclToFullName_1746_);
lean_dec_ref(v_fvarIdToDecl_1745_);
lean_dec_ref(v_decls_1744_);
v_a_1773_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1750_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1750_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_countUsesLCtx_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1737_ = stack[0].m_obj;
lean_object* v_targetUses_1738_ = stack[1].m_obj;
lean_object* v_a_1739_ = stack[2].m_obj;
lean_object* v_a_1740_ = stack[3].m_obj;
lean_object* v_a_1741_ = stack[4].m_obj;
lean_object* v_a_1742_ = stack[5].m_obj;
lean_object* v_res_1781_;
v_res_1781_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1737_, v_targetUses_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
stack->m_obj
 = v_res_1781_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object* v_ctx_1782_, lean_object* v_targetUses_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1782_, v_targetUses_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
return v_res_1789_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t v_sz_1790_, size_t v_i_1791_, lean_object* v_bs_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1790_, v_i_1791_, v_bs_1792_, v___y_1793_);
return v___x_1799_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1790_ = stack[0].m_num;
size_t v_i_1791_ = stack[1].m_num;
lean_object* v_bs_1792_ = stack[2].m_obj;
lean_object* v___y_1793_ = stack[3].m_obj;
lean_object* v___y_1794_ = stack[4].m_obj;
lean_object* v___y_1795_ = stack[5].m_obj;
lean_object* v___y_1796_ = stack[6].m_obj;
lean_object* v___y_1797_ = stack[7].m_obj;
lean_object* v_res_1800_;
v_res_1800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_1790_, v_i_1791_, v_bs_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
stack->m_obj
 = v_res_1800_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object* v_sz_1801_, lean_object* v_i_1802_, lean_object* v_bs_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
size_t v_sz_boxed_1810_; size_t v_i_boxed_1811_; lean_object* v_res_1812_; 
v_sz_boxed_1810_ = lean_unbox_usize(v_sz_1801_);
lean_dec(v_sz_1801_);
v_i_boxed_1811_ = lean_unbox_usize(v_i_1802_);
lean_dec(v_i_1802_);
v_res_1812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_1810_, v_i_boxed_1811_, v_bs_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
return v_res_1812_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t v_u_1813_, lean_object* v_rhs_1814_, uint8_t v_elimTrivial_1815_){
_start:
{
uint8_t v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = 2;
v___x_1817_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_1813_, v___x_1816_);
if (v___x_1817_ == 0)
{
return v___x_1817_;
}
else
{
if (v_elimTrivial_1815_ == 0)
{
return v___x_1817_;
}
else
{
uint8_t v___x_1818_; 
v___x_1818_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_1814_);
if (v___x_1818_ == 0)
{
return v___x_1817_;
}
else
{
uint8_t v___x_1819_; 
v___x_1819_ = 0;
return v___x_1819_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_doNotDup_0interp(lean_interpreter_value* stack)
{
uint8_t v_u_1813_ = stack[0].m_num;
lean_object* v_rhs_1814_ = stack[1].m_obj;
uint8_t v_elimTrivial_1815_ = stack[2].m_num;
uint8_t v_res_1820_;
v_res_1820_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_1813_, v_rhs_1814_, v_elimTrivial_1815_);
stack->m_num = v_res_1820_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object* v_u_1821_, lean_object* v_rhs_1822_, lean_object* v_elimTrivial_1823_){
_start:
{
uint8_t v_u_boxed_1824_; uint8_t v_elimTrivial_boxed_1825_; uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_u_boxed_1824_ = lean_unbox(v_u_1821_);
v_elimTrivial_boxed_1825_ = lean_unbox(v_elimTrivial_1823_);
v_res_1826_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_1824_, v_rhs_1822_, v_elimTrivial_boxed_1825_);
lean_dec_ref(v_rhs_1822_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t v_elimTrivial_1830_, lean_object* v_e_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
if (lean_obj_tag(v_e_1831_) == 8)
{
lean_object* v_type_1838_; 
v_type_1838_ = lean_ctor_get(v_e_1831_, 1);
if (lean_obj_tag(v_type_1838_) == 10)
{
lean_object* v_value_1839_; lean_object* v_body_1840_; lean_object* v_data_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v_uses_1845_; uint8_t v___x_1846_; 
v_value_1839_ = lean_ctor_get(v_e_1831_, 2);
v_body_1840_ = lean_ctor_get(v_e_1831_, 3);
v_data_1841_ = lean_ctor_get(v_type_1838_, 0);
v___x_1842_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_1843_ = lean_unsigned_to_nat(2u);
v___x_1844_ = l_Lean_KVMap_getNat(v_data_1841_, v___x_1842_, v___x_1843_);
v_uses_1845_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_1844_);
lean_dec(v___x_1844_);
v___x_1846_ = l_Lean_Elab_Tactic_Do_doNotDup(v_uses_1845_, v_value_1839_, v_elimTrivial_1830_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_expr_instantiate1(v_body_1840_, v_value_1839_);
v___x_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_elimTrivial_1830_ = stack[0].m_num;
lean_object* v_e_1831_ = stack[1].m_obj;
lean_object* v___y_1832_ = stack[2].m_obj;
lean_object* v___y_1833_ = stack[3].m_obj;
lean_object* v___y_1834_ = stack[4].m_obj;
lean_object* v___y_1835_ = stack[5].m_obj;
lean_object* v___y_1836_ = stack[6].m_obj;
lean_object* v_res_1856_;
v_res_1856_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_1830_, v_e_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
stack->m_obj
 = v_res_1856_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object* v_elimTrivial_1857_, lean_object* v_e_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
uint8_t v_elimTrivial_boxed_1865_; lean_object* v_res_1866_; 
v_elimTrivial_boxed_1865_ = lean_unbox(v_elimTrivial_1857_);
v_res_1866_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_boxed_1865_, v_e_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v_e_1858_);
return v_res_1866_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object* v_e_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1874_, 0, v_e_1867_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1867_ = stack[0].m_obj;
lean_object* v___y_1868_ = stack[1].m_obj;
lean_object* v___y_1869_ = stack[2].m_obj;
lean_object* v___y_1870_ = stack[3].m_obj;
lean_object* v___y_1871_ = stack[4].m_obj;
lean_object* v___y_1872_ = stack[5].m_obj;
lean_object* v_res_1876_;
v_res_1876_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
stack->m_obj
 = v_res_1876_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object* v_e_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
return v_res_1884_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = l_Lean_maxRecDepthErrorMessage;
v___x_1891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_1893_ = l_Lean_MessageData_ofFormat(v___x_1892_);
return v___x_1893_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_1895_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_1896_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v___x_1894_);
return v___x_1896_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v_ref_1897_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1897_ = stack[0].m_obj;
lean_object* v_res_1902_;
v_res_1902_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1897_);
stack->m_obj
 = v_res_1902_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1903_);
return v_res_1905_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object* v_x_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___y_1915_; lean_object* v_toCold_1924_; lean_object* v_currRecDepth_1925_; lean_object* v_ref_1926_; uint16_t v_optionFlags_1927_; uint8_t v_suppressElabErrors_1928_; uint8_t v_isRecordingDeps_1929_; lean_object* v_maxRecDepth_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v_toCold_1924_ = lean_ctor_get(v___y_1911_, 0);
v_currRecDepth_1925_ = lean_ctor_get(v___y_1911_, 1);
v_ref_1926_ = lean_ctor_get(v___y_1911_, 2);
v_optionFlags_1927_ = lean_ctor_get_uint16(v___y_1911_, sizeof(void*)*3);
v_suppressElabErrors_1928_ = lean_ctor_get_uint8(v___y_1911_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1929_ = lean_ctor_get_uint8(v___y_1911_, sizeof(void*)*3 + 3);
v_maxRecDepth_1935_ = lean_ctor_get(v_toCold_1924_, 3);
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_nat_dec_eq(v_maxRecDepth_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
uint8_t v___x_1938_; 
v___x_1938_ = lean_nat_dec_eq(v_currRecDepth_1925_, v_maxRecDepth_1935_);
if (v___x_1938_ == 0)
{
goto v___jp_1930_;
}
else
{
lean_object* v___x_1939_; 
lean_dec_ref(v_x_1906_);
lean_inc(v_ref_1926_);
v___x_1939_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1926_);
v___y_1915_ = v___x_1939_;
goto v___jp_1914_;
}
}
else
{
goto v___jp_1930_;
}
v___jp_1914_:
{
if (lean_obj_tag(v___y_1915_) == 0)
{
return v___y_1915_;
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
v_a_1916_ = lean_ctor_get(v___y_1915_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___y_1915_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___y_1915_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___y_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
v___jp_1930_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1931_ = lean_unsigned_to_nat(1u);
v___x_1932_ = lean_nat_add(v_currRecDepth_1925_, v___x_1931_);
lean_inc(v_ref_1926_);
lean_inc_ref(v_toCold_1924_);
v___x_1933_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1933_, 0, v_toCold_1924_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
lean_ctor_set(v___x_1933_, 2, v_ref_1926_);
lean_ctor_set_uint16(v___x_1933_, sizeof(void*)*3, v_optionFlags_1927_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 2, v_suppressElabErrors_1928_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 3, v_isRecordingDeps_1929_);
lean_inc(v___y_1912_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
lean_inc(v___y_1908_);
lean_inc(v___y_1907_);
v___x_1934_ = lean_apply_7(v_x_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___x_1933_, v___y_1912_, lean_box(0));
v___y_1915_ = v___x_1934_;
goto v___jp_1914_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1906_ = stack[0].m_obj;
lean_object* v___y_1907_ = stack[1].m_obj;
lean_object* v___y_1908_ = stack[2].m_obj;
lean_object* v___y_1909_ = stack[3].m_obj;
lean_object* v___y_1910_ = stack[4].m_obj;
lean_object* v___y_1911_ = stack[5].m_obj;
lean_object* v___y_1912_ = stack[6].m_obj;
lean_object* v_res_1940_;
v_res_1940_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
stack->m_obj
 = v_res_1940_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec(v___y_1942_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_1950_, lean_object* v_x_1951_){
_start:
{
if (lean_obj_tag(v_x_1951_) == 0)
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_box(0);
return v___x_1952_;
}
else
{
lean_object* v_key_1953_; lean_object* v_value_1954_; lean_object* v_tail_1955_; uint8_t v___x_1956_; 
v_key_1953_ = lean_ctor_get(v_x_1951_, 0);
v_value_1954_ = lean_ctor_get(v_x_1951_, 1);
v_tail_1955_ = lean_ctor_get(v_x_1951_, 2);
v___x_1956_ = l_Lean_ExprStructEq_beq(v_key_1953_, v_a_1950_);
if (v___x_1956_ == 0)
{
v_x_1951_ = v_tail_1955_;
goto _start;
}
else
{
lean_object* v___x_1958_; 
lean_inc(v_value_1954_);
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_value_1954_);
return v___x_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_1959_, lean_object* v_x_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1959_, v_x_1960_);
lean_dec(v_x_1960_);
lean_dec_ref(v_a_1959_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_m_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_buckets_1964_; lean_object* v___x_1965_; uint64_t v___x_1966_; uint64_t v___x_1967_; uint64_t v___x_1968_; uint64_t v_fold_1969_; uint64_t v___x_1970_; uint64_t v___x_1971_; uint64_t v___x_1972_; size_t v___x_1973_; size_t v___x_1974_; size_t v___x_1975_; size_t v___x_1976_; size_t v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_buckets_1964_ = lean_ctor_get(v_m_1962_, 1);
v___x_1965_ = lean_array_get_size(v_buckets_1964_);
v___x_1966_ = l_Lean_ExprStructEq_hash(v_a_1963_);
v___x_1967_ = 32ULL;
v___x_1968_ = lean_uint64_shift_right(v___x_1966_, v___x_1967_);
v_fold_1969_ = lean_uint64_xor(v___x_1966_, v___x_1968_);
v___x_1970_ = 16ULL;
v___x_1971_ = lean_uint64_shift_right(v_fold_1969_, v___x_1970_);
v___x_1972_ = lean_uint64_xor(v_fold_1969_, v___x_1971_);
v___x_1973_ = lean_uint64_to_usize(v___x_1972_);
v___x_1974_ = lean_usize_of_nat(v___x_1965_);
v___x_1975_ = ((size_t)1ULL);
v___x_1976_ = lean_usize_sub(v___x_1974_, v___x_1975_);
v___x_1977_ = lean_usize_land(v___x_1973_, v___x_1976_);
v___x_1978_ = lean_array_uget_borrowed(v_buckets_1964_, v___x_1977_);
v___x_1979_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1963_, v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_1980_, v_a_1981_);
lean_dec_ref(v_a_1981_);
lean_dec_ref(v_m_1980_);
return v_res_1982_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v_b_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___x_1992_; 
lean_inc(v___y_1990_);
lean_inc_ref(v___y_1989_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
lean_inc(v___y_1985_);
lean_inc(v___y_1984_);
v___x_1992_ = lean_apply_8(v_k_1983_, v_b_1986_, v___y_1984_, v___y_1985_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, lean_box(0));
return v___x_1992_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1983_ = stack[0].m_obj;
lean_object* v___y_1984_ = stack[1].m_obj;
lean_object* v___y_1985_ = stack[2].m_obj;
lean_object* v_b_1986_ = stack[3].m_obj;
lean_object* v___y_1987_ = stack[4].m_obj;
lean_object* v___y_1988_ = stack[5].m_obj;
lean_object* v___y_1989_ = stack[6].m_obj;
lean_object* v___y_1990_ = stack[7].m_obj;
lean_object* v_res_1993_;
v_res_1993_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1983_, v___y_1984_, v___y_1985_, v_b_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
stack->m_obj
 = v_res_1993_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v_b_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1994_, v___y_1995_, v___y_1996_, v_b_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1996_);
lean_dec(v___y_1995_);
return v_res_2003_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_2004_, lean_object* v_type_2005_, lean_object* v_val_2006_, lean_object* v_k_2007_, uint8_t v_nondep_2008_, uint8_t v_kind_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___f_2017_; lean_object* v___x_2018_; 
lean_inc(v___y_2011_);
lean_inc(v___y_2010_);
v___f_2017_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2017_, 0, v_k_2007_);
lean_closure_set(v___f_2017_, 1, v___y_2010_);
lean_closure_set(v___f_2017_, 2, v___y_2011_);
v___x_2018_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2004_, v_type_2005_, v_val_2006_, v___f_2017_, v_nondep_2008_, v_kind_2009_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2018_) == 0)
{
return v___x_2018_;
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2004_ = stack[0].m_obj;
lean_object* v_type_2005_ = stack[1].m_obj;
lean_object* v_val_2006_ = stack[2].m_obj;
lean_object* v_k_2007_ = stack[3].m_obj;
uint8_t v_nondep_2008_ = stack[4].m_num;
uint8_t v_kind_2009_ = stack[5].m_num;
lean_object* v___y_2010_ = stack[6].m_obj;
lean_object* v___y_2011_ = stack[7].m_obj;
lean_object* v___y_2012_ = stack[8].m_obj;
lean_object* v___y_2013_ = stack[9].m_obj;
lean_object* v___y_2014_ = stack[10].m_obj;
lean_object* v___y_2015_ = stack[11].m_obj;
lean_object* v_res_2027_;
v_res_2027_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_2004_, v_type_2005_, v_val_2006_, v_k_2007_, v_nondep_2008_, v_kind_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
stack->m_obj
 = v_res_2027_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_2028_, lean_object* v_type_2029_, lean_object* v_val_2030_, lean_object* v_k_2031_, lean_object* v_nondep_2032_, lean_object* v_kind_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v_nondep_boxed_2041_; uint8_t v_kind_boxed_2042_; lean_object* v_res_2043_; 
v_nondep_boxed_2041_ = lean_unbox(v_nondep_2032_);
v_kind_boxed_2042_ = lean_unbox(v_kind_2033_);
v_res_2043_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_2028_, v_type_2029_, v_val_2030_, v_k_2031_, v_nondep_boxed_2041_, v_kind_boxed_2042_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec(v___y_2034_);
return v_res_2043_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_2044_, uint8_t v_bi_2045_, lean_object* v_type_2046_, lean_object* v_k_2047_, uint8_t v_kind_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___f_2056_; lean_object* v___x_2057_; 
lean_inc(v___y_2050_);
lean_inc(v___y_2049_);
v___f_2056_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2056_, 0, v_k_2047_);
lean_closure_set(v___f_2056_, 1, v___y_2049_);
lean_closure_set(v___f_2056_, 2, v___y_2050_);
v___x_2057_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2044_, v_bi_2045_, v_type_2046_, v___f_2056_, v_kind_2048_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2057_) == 0)
{
return v___x_2057_;
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2044_ = stack[0].m_obj;
uint8_t v_bi_2045_ = stack[1].m_num;
lean_object* v_type_2046_ = stack[2].m_obj;
lean_object* v_k_2047_ = stack[3].m_obj;
uint8_t v_kind_2048_ = stack[4].m_num;
lean_object* v___y_2049_ = stack[5].m_obj;
lean_object* v___y_2050_ = stack[6].m_obj;
lean_object* v___y_2051_ = stack[7].m_obj;
lean_object* v___y_2052_ = stack[8].m_obj;
lean_object* v___y_2053_ = stack[9].m_obj;
lean_object* v___y_2054_ = stack[10].m_obj;
lean_object* v_res_2066_;
v_res_2066_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2044_, v_bi_2045_, v_type_2046_, v_k_2047_, v_kind_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
stack->m_obj
 = v_res_2066_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_2067_, lean_object* v_bi_2068_, lean_object* v_type_2069_, lean_object* v_k_2070_, lean_object* v_kind_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v_bi_boxed_2079_; uint8_t v_kind_boxed_2080_; lean_object* v_res_2081_; 
v_bi_boxed_2079_ = lean_unbox(v_bi_2068_);
v_kind_boxed_2080_ = lean_unbox(v_kind_2071_);
v_res_2081_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2067_, v_bi_boxed_2079_, v_type_2069_, v_k_2070_, v_kind_boxed_2080_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec(v___y_2072_);
return v_res_2081_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2082_);
return v___x_2089_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2082_ = stack[0].m_obj;
lean_object* v___y_2083_ = stack[1].m_obj;
lean_object* v___y_2084_ = stack[2].m_obj;
lean_object* v___y_2085_ = stack[3].m_obj;
lean_object* v___y_2086_ = stack[4].m_obj;
lean_object* v___y_2087_ = stack[5].m_obj;
lean_object* v_res_2090_;
v_res_2090_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
stack->m_obj
 = v_res_2090_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
return v_res_2098_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2099_, lean_object* v_x_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_apply_1(v_x_2100_, lean_box(0));
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2100_ = stack[1].m_obj;
lean_object* v___y_2101_ = stack[2].m_obj;
lean_object* v___y_2102_ = stack[3].m_obj;
lean_object* v___y_2103_ = stack[4].m_obj;
lean_object* v___y_2104_ = stack[5].m_obj;
lean_object* v___y_2105_ = stack[6].m_obj;
lean_object* v_res_2109_;
v_res_2109_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v_x_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
stack->m_obj
 = v_res_2109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2110_, lean_object* v_x_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2110_, v_x_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_2119_, lean_object* v_x_2120_){
_start:
{
if (lean_obj_tag(v_x_2120_) == 0)
{
return v_x_2119_;
}
else
{
lean_object* v_key_2121_; lean_object* v_value_2122_; lean_object* v_tail_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2146_; 
v_key_2121_ = lean_ctor_get(v_x_2120_, 0);
v_value_2122_ = lean_ctor_get(v_x_2120_, 1);
v_tail_2123_ = lean_ctor_get(v_x_2120_, 2);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_x_2120_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2125_ = v_x_2120_;
v_isShared_2126_ = v_isSharedCheck_2146_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_tail_2123_);
lean_inc(v_value_2122_);
lean_inc(v_key_2121_);
lean_dec(v_x_2120_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2146_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; uint64_t v___x_2128_; uint64_t v___x_2129_; uint64_t v___x_2130_; uint64_t v_fold_2131_; uint64_t v___x_2132_; uint64_t v___x_2133_; uint64_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; size_t v___x_2137_; size_t v___x_2138_; size_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2127_ = lean_array_get_size(v_x_2119_);
v___x_2128_ = l_Lean_ExprStructEq_hash(v_key_2121_);
v___x_2129_ = 32ULL;
v___x_2130_ = lean_uint64_shift_right(v___x_2128_, v___x_2129_);
v_fold_2131_ = lean_uint64_xor(v___x_2128_, v___x_2130_);
v___x_2132_ = 16ULL;
v___x_2133_ = lean_uint64_shift_right(v_fold_2131_, v___x_2132_);
v___x_2134_ = lean_uint64_xor(v_fold_2131_, v___x_2133_);
v___x_2135_ = lean_uint64_to_usize(v___x_2134_);
v___x_2136_ = lean_usize_of_nat(v___x_2127_);
v___x_2137_ = ((size_t)1ULL);
v___x_2138_ = lean_usize_sub(v___x_2136_, v___x_2137_);
v___x_2139_ = lean_usize_land(v___x_2135_, v___x_2138_);
v___x_2140_ = lean_array_uget_borrowed(v_x_2119_, v___x_2139_);
lean_inc(v___x_2140_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 2, v___x_2140_);
v___x_2142_ = v___x_2125_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_key_2121_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_value_2122_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_array_uset(v_x_2119_, v___x_2139_, v___x_2142_);
v_x_2119_ = v___x_2143_;
v_x_2120_ = v_tail_2123_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_2147_, lean_object* v_source_2148_, lean_object* v_target_2149_){
_start:
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = lean_array_get_size(v_source_2148_);
v___x_2151_ = lean_nat_dec_lt(v_i_2147_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_dec_ref(v_source_2148_);
lean_dec(v_i_2147_);
return v_target_2149_;
}
else
{
lean_object* v_es_2152_; lean_object* v___x_2153_; lean_object* v_source_2154_; lean_object* v_target_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_es_2152_ = lean_array_fget(v_source_2148_, v_i_2147_);
v___x_2153_ = lean_box(0);
v_source_2154_ = lean_array_fset(v_source_2148_, v_i_2147_, v___x_2153_);
v_target_2155_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_2149_, v_es_2152_);
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = lean_nat_add(v_i_2147_, v___x_2156_);
lean_dec(v_i_2147_);
v_i_2147_ = v___x_2157_;
v_source_2148_ = v_source_2154_;
v_target_2149_ = v_target_2155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_2159_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v_nbuckets_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2160_ = lean_array_get_size(v_data_2159_);
v___x_2161_ = lean_unsigned_to_nat(2u);
v_nbuckets_2162_ = lean_nat_mul(v___x_2160_, v___x_2161_);
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = lean_box(0);
v___x_2165_ = lean_mk_array(v_nbuckets_2162_, v___x_2164_);
v___x_2166_ = lean_array_propagate_mark(v_data_2159_, v___x_2165_);
v___x_2167_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_2163_, v_data_2159_, v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_2168_, lean_object* v_b_2169_, lean_object* v_x_2170_){
_start:
{
if (lean_obj_tag(v_x_2170_) == 0)
{
lean_dec(v_b_2169_);
lean_dec_ref(v_a_2168_);
return v_x_2170_;
}
else
{
lean_object* v_key_2171_; lean_object* v_value_2172_; lean_object* v_tail_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2185_; 
v_key_2171_ = lean_ctor_get(v_x_2170_, 0);
v_value_2172_ = lean_ctor_get(v_x_2170_, 1);
v_tail_2173_ = lean_ctor_get(v_x_2170_, 2);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_x_2170_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2175_ = v_x_2170_;
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_tail_2173_);
lean_inc(v_value_2172_);
lean_inc(v_key_2171_);
lean_dec(v_x_2170_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
uint8_t v___x_2177_; 
v___x_2177_ = l_Lean_ExprStructEq_beq(v_key_2171_, v_a_2168_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2178_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2168_, v_b_2169_, v_tail_2173_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 2, v___x_2178_);
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_key_2171_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_value_2172_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
else
{
lean_object* v___x_2183_; 
lean_dec(v_value_2172_);
lean_dec(v_key_2171_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 1, v_b_2169_);
lean_ctor_set(v___x_2175_, 0, v_a_2168_);
v___x_2183_ = v___x_2175_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2168_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_b_2169_);
lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_tail_2173_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_2186_, lean_object* v_x_2187_){
_start:
{
if (lean_obj_tag(v_x_2187_) == 0)
{
uint8_t v___x_2188_; 
v___x_2188_ = 0;
return v___x_2188_;
}
else
{
lean_object* v_key_2189_; lean_object* v_tail_2190_; uint8_t v___x_2191_; 
v_key_2189_ = lean_ctor_get(v_x_2187_, 0);
v_tail_2190_ = lean_ctor_get(v_x_2187_, 2);
v___x_2191_ = l_Lean_ExprStructEq_beq(v_key_2189_, v_a_2186_);
if (v___x_2191_ == 0)
{
v_x_2187_ = v_tail_2190_;
goto _start;
}
else
{
return v___x_2191_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2186_ = stack[0].m_obj;
lean_object* v_x_2187_ = stack[1].m_obj;
uint8_t v_res_2193_;
v_res_2193_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2186_, v_x_2187_);
stack->m_num = v_res_2193_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_2194_, lean_object* v_x_2195_){
_start:
{
uint8_t v_res_2196_; lean_object* v_r_2197_; 
v_res_2196_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2194_, v_x_2195_);
lean_dec(v_x_2195_);
lean_dec_ref(v_a_2194_);
v_r_2197_ = lean_box(v_res_2196_);
return v_r_2197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2198_, lean_object* v_a_2199_, lean_object* v_b_2200_){
_start:
{
lean_object* v_size_2201_; lean_object* v_buckets_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2245_; 
v_size_2201_ = lean_ctor_get(v_m_2198_, 0);
v_buckets_2202_ = lean_ctor_get(v_m_2198_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_m_2198_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2204_ = v_m_2198_;
v_isShared_2205_ = v_isSharedCheck_2245_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_buckets_2202_);
lean_inc(v_size_2201_);
lean_dec(v_m_2198_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2245_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; uint64_t v___x_2207_; uint64_t v___x_2208_; uint64_t v___x_2209_; uint64_t v_fold_2210_; uint64_t v___x_2211_; uint64_t v___x_2212_; uint64_t v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; size_t v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; lean_object* v_bkt_2219_; uint8_t v___x_2220_; 
v___x_2206_ = lean_array_get_size(v_buckets_2202_);
v___x_2207_ = l_Lean_ExprStructEq_hash(v_a_2199_);
v___x_2208_ = 32ULL;
v___x_2209_ = lean_uint64_shift_right(v___x_2207_, v___x_2208_);
v_fold_2210_ = lean_uint64_xor(v___x_2207_, v___x_2209_);
v___x_2211_ = 16ULL;
v___x_2212_ = lean_uint64_shift_right(v_fold_2210_, v___x_2211_);
v___x_2213_ = lean_uint64_xor(v_fold_2210_, v___x_2212_);
v___x_2214_ = lean_uint64_to_usize(v___x_2213_);
v___x_2215_ = lean_usize_of_nat(v___x_2206_);
v___x_2216_ = ((size_t)1ULL);
v___x_2217_ = lean_usize_sub(v___x_2215_, v___x_2216_);
v___x_2218_ = lean_usize_land(v___x_2214_, v___x_2217_);
v_bkt_2219_ = lean_array_uget_borrowed(v_buckets_2202_, v___x_2218_);
v___x_2220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2199_, v_bkt_2219_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; lean_object* v_size_x27_2222_; lean_object* v___x_2223_; lean_object* v_buckets_x27_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2221_ = lean_unsigned_to_nat(1u);
v_size_x27_2222_ = lean_nat_add(v_size_2201_, v___x_2221_);
lean_dec(v_size_2201_);
lean_inc(v_bkt_2219_);
v___x_2223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2223_, 0, v_a_2199_);
lean_ctor_set(v___x_2223_, 1, v_b_2200_);
lean_ctor_set(v___x_2223_, 2, v_bkt_2219_);
v_buckets_x27_2224_ = lean_array_uset(v_buckets_2202_, v___x_2218_, v___x_2223_);
v___x_2225_ = lean_unsigned_to_nat(4u);
v___x_2226_ = lean_nat_mul(v_size_x27_2222_, v___x_2225_);
v___x_2227_ = lean_unsigned_to_nat(3u);
v___x_2228_ = lean_nat_div(v___x_2226_, v___x_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_array_get_size(v_buckets_x27_2224_);
v___x_2230_ = lean_nat_dec_le(v___x_2228_, v___x_2229_);
lean_dec(v___x_2228_);
if (v___x_2230_ == 0)
{
lean_object* v_val_2231_; lean_object* v___x_2233_; 
v_val_2231_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_2224_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v_val_2231_);
lean_ctor_set(v___x_2204_, 0, v_size_x27_2222_);
v___x_2233_ = v___x_2204_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_size_x27_2222_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_val_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
else
{
lean_object* v___x_2236_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v_buckets_x27_2224_);
lean_ctor_set(v___x_2204_, 0, v_size_x27_2222_);
v___x_2236_ = v___x_2204_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_size_x27_2222_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_buckets_x27_2224_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v_buckets_x27_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2243_; 
lean_inc(v_bkt_2219_);
v___x_2238_ = lean_box(0);
v_buckets_x27_2239_ = lean_array_uset(v_buckets_2202_, v___x_2218_, v___x_2238_);
v___x_2240_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2199_, v_b_2200_, v_bkt_2219_);
v___x_2241_ = lean_array_uset(v_buckets_x27_2239_, v___x_2218_, v___x_2240_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v___x_2241_);
v___x_2243_ = v___x_2204_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_size_2201_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2246_, lean_object* v_e_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2250_ = lean_st_ref_take(v_a_2246_);
v___x_2251_ = lean_box(0);
v___x_2252_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2250_, v_e_2247_, v_a_2248_);
v___x_2253_ = lean_st_ref_put(v_a_2246_, v___x_2252_);
return v___x_2251_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2246_ = stack[0].m_obj;
lean_object* v_e_2247_ = stack[1].m_obj;
lean_object* v_a_2248_ = stack[2].m_obj;
lean_object* v_res_2254_;
v_res_2254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2246_, v_e_2247_, v_a_2248_);
stack->m_obj
 = v_res_2254_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2255_, lean_object* v_e_2256_, lean_object* v_a_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2255_, v_e_2256_, v_a_2257_);
lean_dec(v_a_2255_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2260_, lean_object* v_pre_2261_, lean_object* v_post_2262_, lean_object* v_usedLetOnly_2263_, lean_object* v_skipConstInApp_2264_, lean_object* v_skipInstances_2265_, lean_object* v_body_2266_, lean_object* v_x_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
uint8_t v_usedLetOnly_boxed_2275_; uint8_t v_skipConstInApp_boxed_2276_; uint8_t v_skipInstances_boxed_2277_; lean_object* v_res_2278_; 
v_usedLetOnly_boxed_2275_ = lean_unbox(v_usedLetOnly_2263_);
v_skipConstInApp_boxed_2276_ = lean_unbox(v_skipConstInApp_2264_);
v_skipInstances_boxed_2277_ = lean_unbox(v_skipInstances_2265_);
v_res_2278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2260_, v_pre_2261_, v_post_2262_, v_usedLetOnly_boxed_2275_, v_skipConstInApp_boxed_2276_, v_skipInstances_boxed_2277_, v_body_2266_, v_x_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec(v___y_2268_);
return v_res_2278_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_2282_, lean_object* v_pre_2283_, lean_object* v_post_2284_, uint8_t v_usedLetOnly_2285_, uint8_t v_skipConstInApp_2286_, uint8_t v_skipInstances_2287_, lean_object* v_body_2288_, lean_object* v_x_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_array_push(v_fvars_2282_, v_x_2289_);
v___x_2298_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2283_, v_post_2284_, v_usedLetOnly_2285_, v_skipConstInApp_2286_, v_skipInstances_2287_, v___x_2297_, v_body_2288_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2298_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2282_ = stack[0].m_obj;
lean_object* v_pre_2283_ = stack[1].m_obj;
lean_object* v_post_2284_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2285_ = stack[3].m_num;
uint8_t v_skipConstInApp_2286_ = stack[4].m_num;
uint8_t v_skipInstances_2287_ = stack[5].m_num;
lean_object* v_body_2288_ = stack[6].m_obj;
lean_object* v_x_2289_ = stack[7].m_obj;
lean_object* v___y_2290_ = stack[8].m_obj;
lean_object* v___y_2291_ = stack[9].m_obj;
lean_object* v___y_2292_ = stack[10].m_obj;
lean_object* v___y_2293_ = stack[11].m_obj;
lean_object* v___y_2294_ = stack[12].m_obj;
lean_object* v___y_2295_ = stack[13].m_obj;
lean_object* v_res_2299_;
v_res_2299_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2282_, v_pre_2283_, v_post_2284_, v_usedLetOnly_2285_, v_skipConstInApp_2286_, v_skipInstances_2287_, v_body_2288_, v_x_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
stack->m_obj
 = v_res_2299_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_2300_, lean_object* v_pre_2301_, lean_object* v_post_2302_, lean_object* v_usedLetOnly_2303_, lean_object* v_skipConstInApp_2304_, lean_object* v_skipInstances_2305_, lean_object* v_body_2306_, lean_object* v_x_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
uint8_t v_usedLetOnly_boxed_2315_; uint8_t v_skipConstInApp_boxed_2316_; uint8_t v_skipInstances_boxed_2317_; lean_object* v_res_2318_; 
v_usedLetOnly_boxed_2315_ = lean_unbox(v_usedLetOnly_2303_);
v_skipConstInApp_boxed_2316_ = lean_unbox(v_skipConstInApp_2304_);
v_skipInstances_boxed_2317_ = lean_unbox(v_skipInstances_2305_);
v_res_2318_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2300_, v_pre_2301_, v_post_2302_, v_usedLetOnly_boxed_2315_, v_skipConstInApp_boxed_2316_, v_skipInstances_boxed_2317_, v_body_2306_, v_x_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec(v___y_2308_);
return v_res_2318_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object* v_pre_2319_, lean_object* v_post_2320_, uint8_t v_usedLetOnly_2321_, uint8_t v_skipConstInApp_2322_, uint8_t v_skipInstances_2323_, lean_object* v_e_2324_, lean_object* v_a_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v___x_2332_; 
lean_inc_ref(v_post_2320_);
lean_inc(v___y_2330_);
lean_inc_ref(v___y_2329_);
lean_inc(v___y_2328_);
lean_inc_ref(v___y_2327_);
lean_inc(v___y_2326_);
lean_inc_ref(v_e_2324_);
v___x_2332_ = lean_apply_7(v_post_2320_, v_e_2324_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, lean_box(0));
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2351_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2351_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2351_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
switch(lean_obj_tag(v_a_2333_))
{
case 0:
{
lean_object* v_e_2337_; lean_object* v___x_2339_; 
lean_dec_ref(v_e_2324_);
lean_dec_ref(v_post_2320_);
lean_dec_ref(v_pre_2319_);
v_e_2337_ = lean_ctor_get(v_a_2333_, 0);
lean_inc_ref(v_e_2337_);
lean_dec_ref_known(v_a_2333_, 1);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v_e_2337_);
v___x_2339_ = v___x_2335_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_e_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
case 1:
{
lean_object* v_e_2341_; lean_object* v___x_2342_; 
lean_del_object(v___x_2335_);
lean_dec_ref(v_e_2324_);
v_e_2341_ = lean_ctor_get(v_a_2333_, 0);
lean_inc_ref(v_e_2341_);
lean_dec_ref_known(v_a_2333_, 1);
v___x_2342_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2319_, v_post_2320_, v_usedLetOnly_2321_, v_skipConstInApp_2322_, v_skipInstances_2323_, v_e_2341_, v_a_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
return v___x_2342_;
}
default: 
{
lean_object* v_e_x3f_2343_; 
lean_dec_ref(v_post_2320_);
lean_dec_ref(v_pre_2319_);
v_e_x3f_2343_ = lean_ctor_get(v_a_2333_, 0);
lean_inc(v_e_x3f_2343_);
lean_dec_ref_known(v_a_2333_, 1);
if (lean_obj_tag(v_e_x3f_2343_) == 0)
{
lean_object* v___x_2345_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v_e_2324_);
v___x_2345_ = v___x_2335_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_e_2324_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
else
{
lean_object* v_val_2347_; lean_object* v___x_2349_; 
lean_dec_ref(v_e_2324_);
v_val_2347_ = lean_ctor_get(v_e_x3f_2343_, 0);
lean_inc(v_val_2347_);
lean_dec_ref_known(v_e_x3f_2343_, 1);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v_val_2347_);
v___x_2349_ = v___x_2335_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_val_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v_e_2324_);
lean_dec_ref(v_post_2320_);
lean_dec_ref(v_pre_2319_);
v_a_2352_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2332_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2332_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2319_ = stack[0].m_obj;
lean_object* v_post_2320_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2321_ = stack[2].m_num;
uint8_t v_skipConstInApp_2322_ = stack[3].m_num;
uint8_t v_skipInstances_2323_ = stack[4].m_num;
lean_object* v_e_2324_ = stack[5].m_obj;
lean_object* v_a_2325_ = stack[6].m_obj;
lean_object* v___y_2326_ = stack[7].m_obj;
lean_object* v___y_2327_ = stack[8].m_obj;
lean_object* v___y_2328_ = stack[9].m_obj;
lean_object* v___y_2329_ = stack[10].m_obj;
lean_object* v___y_2330_ = stack[11].m_obj;
lean_object* v_res_2360_;
v_res_2360_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2319_, v_post_2320_, v_usedLetOnly_2321_, v_skipConstInApp_2322_, v_skipInstances_2323_, v_e_2324_, v_a_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
stack->m_obj
 = v_res_2360_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object* v_pre_2361_, lean_object* v_post_2362_, uint8_t v_usedLetOnly_2363_, uint8_t v_skipConstInApp_2364_, uint8_t v_skipInstances_2365_, lean_object* v_fvars_2366_, lean_object* v_e_2367_, lean_object* v_a_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
if (lean_obj_tag(v_e_2367_) == 6)
{
lean_object* v_binderName_2375_; lean_object* v_binderType_2376_; lean_object* v_body_2377_; uint8_t v_binderInfo_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_binderName_2375_ = lean_ctor_get(v_e_2367_, 0);
lean_inc(v_binderName_2375_);
v_binderType_2376_ = lean_ctor_get(v_e_2367_, 1);
lean_inc_ref(v_binderType_2376_);
v_body_2377_ = lean_ctor_get(v_e_2367_, 2);
lean_inc_ref(v_body_2377_);
v_binderInfo_2378_ = lean_ctor_get_uint8(v_e_2367_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2367_, 3);
v___x_2379_ = lean_box(v_usedLetOnly_2363_);
v___x_2380_ = lean_box(v_skipConstInApp_2364_);
v___x_2381_ = lean_box(v_skipInstances_2365_);
lean_inc_ref(v_post_2362_);
lean_inc_ref(v_pre_2361_);
lean_inc_ref(v_fvars_2366_);
v___f_2382_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2382_, 0, v_fvars_2366_);
lean_closure_set(v___f_2382_, 1, v_pre_2361_);
lean_closure_set(v___f_2382_, 2, v_post_2362_);
lean_closure_set(v___f_2382_, 3, v___x_2379_);
lean_closure_set(v___f_2382_, 4, v___x_2380_);
lean_closure_set(v___f_2382_, 5, v___x_2381_);
lean_closure_set(v___f_2382_, 6, v_body_2377_);
v___x_2383_ = lean_expr_instantiate_rev(v_binderType_2376_, v_fvars_2366_);
lean_dec_ref(v_fvars_2366_);
lean_dec_ref(v_binderType_2376_);
v___x_2384_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2361_, v_post_2362_, v_usedLetOnly_2363_, v_skipConstInApp_2364_, v_skipInstances_2365_, v___x_2383_, v_a_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; uint8_t v___x_2386_; lean_object* v___x_2387_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v___x_2386_ = 0;
v___x_2387_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2375_, v_binderInfo_2378_, v_a_2385_, v___f_2382_, v___x_2386_, v_a_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
return v___x_2387_;
}
else
{
lean_dec_ref(v___f_2382_);
lean_dec(v_binderName_2375_);
return v___x_2384_;
}
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = lean_expr_instantiate_rev(v_e_2367_, v_fvars_2366_);
lean_dec_ref(v_e_2367_);
lean_inc_ref(v_post_2362_);
lean_inc_ref(v_pre_2361_);
v___x_2389_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2361_, v_post_2362_, v_usedLetOnly_2363_, v_skipConstInApp_2364_, v_skipInstances_2365_, v___x_2388_, v_a_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; uint8_t v___x_2391_; uint8_t v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = 0;
v___x_2392_ = 1;
v___x_2393_ = 1;
v___x_2394_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2366_, v_a_2390_, v___x_2391_, v_usedLetOnly_2363_, v___x_2391_, v___x_2392_, v___x_2393_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec_ref(v_fvars_2366_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2396_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v___x_2396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2361_, v_post_2362_, v_usedLetOnly_2363_, v_skipConstInApp_2364_, v_skipInstances_2365_, v_a_2395_, v_a_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
return v___x_2396_;
}
else
{
lean_dec_ref(v_post_2362_);
lean_dec_ref(v_pre_2361_);
return v___x_2394_;
}
}
else
{
lean_dec_ref(v_fvars_2366_);
lean_dec_ref(v_post_2362_);
lean_dec_ref(v_pre_2361_);
return v___x_2389_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2361_ = stack[0].m_obj;
lean_object* v_post_2362_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2363_ = stack[2].m_num;
uint8_t v_skipConstInApp_2364_ = stack[3].m_num;
uint8_t v_skipInstances_2365_ = stack[4].m_num;
lean_object* v_fvars_2366_ = stack[5].m_obj;
lean_object* v_e_2367_ = stack[6].m_obj;
lean_object* v_a_2368_ = stack[7].m_obj;
lean_object* v___y_2369_ = stack[8].m_obj;
lean_object* v___y_2370_ = stack[9].m_obj;
lean_object* v___y_2371_ = stack[10].m_obj;
lean_object* v___y_2372_ = stack[11].m_obj;
lean_object* v___y_2373_ = stack[12].m_obj;
lean_object* v_res_2397_;
v_res_2397_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2361_, v_post_2362_, v_usedLetOnly_2363_, v_skipConstInApp_2364_, v_skipInstances_2365_, v_fvars_2366_, v_e_2367_, v_a_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
stack->m_obj
 = v_res_2397_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_2398_, lean_object* v_pre_2399_, lean_object* v_post_2400_, uint8_t v_usedLetOnly_2401_, uint8_t v_skipConstInApp_2402_, uint8_t v_skipInstances_2403_, lean_object* v_body_2404_, lean_object* v_x_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_array_push(v_fvars_2398_, v_x_2405_);
v___x_2414_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2399_, v_post_2400_, v_usedLetOnly_2401_, v_skipConstInApp_2402_, v_skipInstances_2403_, v___x_2413_, v_body_2404_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
return v___x_2414_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2398_ = stack[0].m_obj;
lean_object* v_pre_2399_ = stack[1].m_obj;
lean_object* v_post_2400_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2401_ = stack[3].m_num;
uint8_t v_skipConstInApp_2402_ = stack[4].m_num;
uint8_t v_skipInstances_2403_ = stack[5].m_num;
lean_object* v_body_2404_ = stack[6].m_obj;
lean_object* v_x_2405_ = stack[7].m_obj;
lean_object* v___y_2406_ = stack[8].m_obj;
lean_object* v___y_2407_ = stack[9].m_obj;
lean_object* v___y_2408_ = stack[10].m_obj;
lean_object* v___y_2409_ = stack[11].m_obj;
lean_object* v___y_2410_ = stack[12].m_obj;
lean_object* v___y_2411_ = stack[13].m_obj;
lean_object* v_res_2415_;
v_res_2415_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2398_, v_pre_2399_, v_post_2400_, v_usedLetOnly_2401_, v_skipConstInApp_2402_, v_skipInstances_2403_, v_body_2404_, v_x_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
stack->m_obj
 = v_res_2415_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_2416_, lean_object* v_pre_2417_, lean_object* v_post_2418_, lean_object* v_usedLetOnly_2419_, lean_object* v_skipConstInApp_2420_, lean_object* v_skipInstances_2421_, lean_object* v_body_2422_, lean_object* v_x_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
uint8_t v_usedLetOnly_boxed_2431_; uint8_t v_skipConstInApp_boxed_2432_; uint8_t v_skipInstances_boxed_2433_; lean_object* v_res_2434_; 
v_usedLetOnly_boxed_2431_ = lean_unbox(v_usedLetOnly_2419_);
v_skipConstInApp_boxed_2432_ = lean_unbox(v_skipConstInApp_2420_);
v_skipInstances_boxed_2433_ = lean_unbox(v_skipInstances_2421_);
v_res_2434_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2416_, v_pre_2417_, v_post_2418_, v_usedLetOnly_boxed_2431_, v_skipConstInApp_boxed_2432_, v_skipInstances_boxed_2433_, v_body_2422_, v_x_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec(v___y_2424_);
return v_res_2434_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object* v_pre_2435_, lean_object* v_post_2436_, uint8_t v_usedLetOnly_2437_, uint8_t v_skipConstInApp_2438_, uint8_t v_skipInstances_2439_, lean_object* v_fvars_2440_, lean_object* v_e_2441_, lean_object* v_a_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
if (lean_obj_tag(v_e_2441_) == 8)
{
lean_object* v_declName_2449_; lean_object* v_type_2450_; lean_object* v_value_2451_; lean_object* v_body_2452_; uint8_t v_nondep_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v_declName_2449_ = lean_ctor_get(v_e_2441_, 0);
lean_inc(v_declName_2449_);
v_type_2450_ = lean_ctor_get(v_e_2441_, 1);
lean_inc_ref(v_type_2450_);
v_value_2451_ = lean_ctor_get(v_e_2441_, 2);
lean_inc_ref(v_value_2451_);
v_body_2452_ = lean_ctor_get(v_e_2441_, 3);
lean_inc_ref(v_body_2452_);
v_nondep_2453_ = lean_ctor_get_uint8(v_e_2441_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2441_, 4);
v___x_2454_ = lean_box(v_usedLetOnly_2437_);
v___x_2455_ = lean_box(v_skipConstInApp_2438_);
v___x_2456_ = lean_box(v_skipInstances_2439_);
lean_inc_ref_n(v_post_2436_, 2);
lean_inc_ref_n(v_pre_2435_, 2);
lean_inc_ref(v_fvars_2440_);
v___f_2457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2457_, 0, v_fvars_2440_);
lean_closure_set(v___f_2457_, 1, v_pre_2435_);
lean_closure_set(v___f_2457_, 2, v_post_2436_);
lean_closure_set(v___f_2457_, 3, v___x_2454_);
lean_closure_set(v___f_2457_, 4, v___x_2455_);
lean_closure_set(v___f_2457_, 5, v___x_2456_);
lean_closure_set(v___f_2457_, 6, v_body_2452_);
v___x_2458_ = lean_expr_instantiate_rev(v_type_2450_, v_fvars_2440_);
lean_dec_ref(v_type_2450_);
v___x_2459_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2435_, v_post_2436_, v_usedLetOnly_2437_, v_skipConstInApp_2438_, v_skipInstances_2439_, v___x_2458_, v_a_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v___x_2461_ = lean_expr_instantiate_rev(v_value_2451_, v_fvars_2440_);
lean_dec_ref(v_fvars_2440_);
lean_dec_ref(v_value_2451_);
v___x_2462_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2435_, v_post_2436_, v_usedLetOnly_2437_, v_skipConstInApp_2438_, v_skipInstances_2439_, v___x_2461_, v_a_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; uint8_t v___x_2464_; lean_object* v___x_2465_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2462_, 1);
v___x_2464_ = 0;
v___x_2465_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2449_, v_a_2460_, v_a_2463_, v___f_2457_, v_nondep_2453_, v___x_2464_, v_a_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
return v___x_2465_;
}
else
{
lean_dec(v_a_2460_);
lean_dec_ref(v___f_2457_);
lean_dec(v_declName_2449_);
return v___x_2462_;
}
}
else
{
lean_dec_ref(v___f_2457_);
lean_dec_ref(v_value_2451_);
lean_dec(v_declName_2449_);
lean_dec_ref(v_fvars_2440_);
lean_dec_ref(v_post_2436_);
lean_dec_ref(v_pre_2435_);
return v___x_2459_;
}
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_expr_instantiate_rev(v_e_2441_, v_fvars_2440_);
lean_dec_ref(v_e_2441_);
lean_inc_ref(v_post_2436_);
lean_inc_ref(v_pre_2435_);
v___x_2467_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2435_, v_post_2436_, v_usedLetOnly_2437_, v_skipConstInApp_2438_, v_skipInstances_2439_, v___x_2466_, v_a_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; uint8_t v___x_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2469_ = 0;
v___x_2470_ = 1;
v___x_2471_ = l_Lean_Meta_mkLetFVars(v_fvars_2440_, v_a_2468_, v_usedLetOnly_2437_, v___x_2469_, v___x_2470_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
lean_dec_ref(v_fvars_2440_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2473_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___x_2471_, 1);
v___x_2473_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2435_, v_post_2436_, v_usedLetOnly_2437_, v_skipConstInApp_2438_, v_skipInstances_2439_, v_a_2472_, v_a_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
return v___x_2473_;
}
else
{
lean_dec_ref(v_post_2436_);
lean_dec_ref(v_pre_2435_);
return v___x_2471_;
}
}
else
{
lean_dec_ref(v_fvars_2440_);
lean_dec_ref(v_post_2436_);
lean_dec_ref(v_pre_2435_);
return v___x_2467_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2435_ = stack[0].m_obj;
lean_object* v_post_2436_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2437_ = stack[2].m_num;
uint8_t v_skipConstInApp_2438_ = stack[3].m_num;
uint8_t v_skipInstances_2439_ = stack[4].m_num;
lean_object* v_fvars_2440_ = stack[5].m_obj;
lean_object* v_e_2441_ = stack[6].m_obj;
lean_object* v_a_2442_ = stack[7].m_obj;
lean_object* v___y_2443_ = stack[8].m_obj;
lean_object* v___y_2444_ = stack[9].m_obj;
lean_object* v___y_2445_ = stack[10].m_obj;
lean_object* v___y_2446_ = stack[11].m_obj;
lean_object* v___y_2447_ = stack[12].m_obj;
lean_object* v_res_2474_;
v_res_2474_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2435_, v_post_2436_, v_usedLetOnly_2437_, v_skipConstInApp_2438_, v_skipInstances_2439_, v_fvars_2440_, v_e_2441_, v_a_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
stack->m_obj
 = v_res_2474_;
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2475_; lean_object* v_dummy_2476_; 
v___x_2475_ = lean_box(0);
v_dummy_2476_ = l_Lean_Expr_sort___override(v___x_2475_);
return v_dummy_2476_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object* v_pre_2477_, lean_object* v_post_2478_, uint8_t v_usedLetOnly_2479_, uint8_t v_skipConstInApp_2480_, uint8_t v_skipInstances_2481_, size_t v_sz_2482_, size_t v_i_2483_, lean_object* v_bs_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
uint8_t v___x_2492_; 
v___x_2492_ = lean_usize_dec_lt(v_i_2483_, v_sz_2482_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
lean_dec_ref(v_post_2478_);
lean_dec_ref(v_pre_2477_);
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v_bs_2484_);
return v___x_2493_;
}
else
{
lean_object* v_v_2494_; lean_object* v___x_2495_; lean_object* v_bs_x27_2496_; lean_object* v___x_2497_; 
v_v_2494_ = lean_array_uget(v_bs_2484_, v_i_2483_);
v___x_2495_ = lean_unsigned_to_nat(0u);
v_bs_x27_2496_ = lean_array_uset(v_bs_2484_, v_i_2483_, v___x_2495_);
lean_inc_ref(v_post_2478_);
lean_inc_ref(v_pre_2477_);
v___x_2497_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2477_, v_post_2478_, v_usedLetOnly_2479_, v_skipConstInApp_2480_, v_skipInstances_2481_, v_v_2494_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; size_t v___x_2499_; size_t v___x_2500_; lean_object* v___x_2501_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = ((size_t)1ULL);
v___x_2500_ = lean_usize_add(v_i_2483_, v___x_2499_);
v___x_2501_ = lean_array_uset(v_bs_x27_2496_, v_i_2483_, v_a_2498_);
v_i_2483_ = v___x_2500_;
v_bs_2484_ = v___x_2501_;
goto _start;
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec_ref(v_bs_x27_2496_);
lean_dec_ref(v_post_2478_);
lean_dec_ref(v_pre_2477_);
v_a_2503_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2497_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2497_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2477_ = stack[0].m_obj;
lean_object* v_post_2478_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2479_ = stack[2].m_num;
uint8_t v_skipConstInApp_2480_ = stack[3].m_num;
uint8_t v_skipInstances_2481_ = stack[4].m_num;
size_t v_sz_2482_ = stack[5].m_num;
size_t v_i_2483_ = stack[6].m_num;
lean_object* v_bs_2484_ = stack[7].m_obj;
lean_object* v___y_2485_ = stack[8].m_obj;
lean_object* v___y_2486_ = stack[9].m_obj;
lean_object* v___y_2487_ = stack[10].m_obj;
lean_object* v___y_2488_ = stack[11].m_obj;
lean_object* v___y_2489_ = stack[12].m_obj;
lean_object* v___y_2490_ = stack[13].m_obj;
lean_object* v_res_2511_;
v_res_2511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2477_, v_post_2478_, v_usedLetOnly_2479_, v_skipConstInApp_2480_, v_skipInstances_2481_, v_sz_2482_, v_i_2483_, v_bs_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
stack->m_obj
 = v_res_2511_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_2512_, lean_object* v_post_2513_, uint8_t v_usedLetOnly_2514_, uint8_t v_skipConstInApp_2515_, uint8_t v_skipInstances_2516_, lean_object* v___x_2517_, lean_object* v___y_2518_, lean_object* v_b_2519_, lean_object* v_a_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2512_, v_post_2513_, v_usedLetOnly_2514_, v_skipConstInApp_2515_, v_skipInstances_2516_, v___x_2517_, v___y_2518_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2537_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2530_ = v___x_2527_;
v_isShared_2531_ = v_isSharedCheck_2537_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2527_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2537_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2532_ = lean_array_fset(v_b_2519_, v_a_2520_, v_a_2528_);
v___x_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v___x_2533_);
v___x_2535_ = v___x_2530_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec_ref(v_b_2519_);
v_a_2538_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2527_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2527_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2512_ = stack[0].m_obj;
lean_object* v_post_2513_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2514_ = stack[2].m_num;
uint8_t v_skipConstInApp_2515_ = stack[3].m_num;
uint8_t v_skipInstances_2516_ = stack[4].m_num;
lean_object* v___x_2517_ = stack[5].m_obj;
lean_object* v___y_2518_ = stack[6].m_obj;
lean_object* v_b_2519_ = stack[7].m_obj;
lean_object* v_a_2520_ = stack[8].m_obj;
lean_object* v___y_2521_ = stack[9].m_obj;
lean_object* v___y_2522_ = stack[10].m_obj;
lean_object* v___y_2523_ = stack[11].m_obj;
lean_object* v___y_2524_ = stack[12].m_obj;
lean_object* v___y_2525_ = stack[13].m_obj;
lean_object* v_res_2546_;
v_res_2546_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2512_, v_post_2513_, v_usedLetOnly_2514_, v_skipConstInApp_2515_, v_skipInstances_2516_, v___x_2517_, v___y_2518_, v_b_2519_, v_a_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
stack->m_obj
 = v_res_2546_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_2547_, lean_object* v_post_2548_, lean_object* v_usedLetOnly_2549_, lean_object* v_skipConstInApp_2550_, lean_object* v_skipInstances_2551_, lean_object* v___x_2552_, lean_object* v___y_2553_, lean_object* v_b_2554_, lean_object* v_a_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
uint8_t v_usedLetOnly_boxed_2562_; uint8_t v_skipConstInApp_boxed_2563_; uint8_t v_skipInstances_boxed_2564_; lean_object* v_res_2565_; 
v_usedLetOnly_boxed_2562_ = lean_unbox(v_usedLetOnly_2549_);
v_skipConstInApp_boxed_2563_ = lean_unbox(v_skipConstInApp_2550_);
v_skipInstances_boxed_2564_ = lean_unbox(v_skipInstances_2551_);
v_res_2565_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2547_, v_post_2548_, v_usedLetOnly_boxed_2562_, v_skipConstInApp_boxed_2563_, v_skipInstances_boxed_2564_, v___x_2552_, v___y_2553_, v_b_2554_, v_a_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec(v_a_2555_);
lean_dec(v___y_2553_);
return v_res_2565_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_2566_, lean_object* v___x_2567_, lean_object* v_pre_2568_, lean_object* v_post_2569_, uint8_t v_usedLetOnly_2570_, uint8_t v_skipConstInApp_2571_, uint8_t v_skipInstances_2572_, lean_object* v_a_2573_, lean_object* v_b_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___y_2583_; uint8_t v___x_2606_; 
v___x_2606_ = lean_nat_dec_lt(v_a_2573_, v_upperBound_2566_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; 
lean_dec(v_a_2573_);
lean_dec_ref(v_post_2569_);
lean_dec_ref(v_pre_2568_);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v_b_2574_);
return v___x_2607_;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2608_ = lean_array_fget_borrowed(v_b_2574_, v_a_2573_);
v___x_2609_ = lean_array_get_size(v___x_2567_);
v___x_2610_ = lean_nat_dec_lt(v_a_2573_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___f_2614_; 
lean_inc(v___x_2608_);
v___x_2611_ = lean_box(v_usedLetOnly_2570_);
v___x_2612_ = lean_box(v_skipConstInApp_2571_);
v___x_2613_ = lean_box(v_skipInstances_2572_);
lean_inc(v_a_2573_);
lean_inc(v___y_2575_);
lean_inc_ref(v_post_2569_);
lean_inc_ref(v_pre_2568_);
v___f_2614_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2614_, 0, v_pre_2568_);
lean_closure_set(v___f_2614_, 1, v_post_2569_);
lean_closure_set(v___f_2614_, 2, v___x_2611_);
lean_closure_set(v___f_2614_, 3, v___x_2612_);
lean_closure_set(v___f_2614_, 4, v___x_2613_);
lean_closure_set(v___f_2614_, 5, v___x_2608_);
lean_closure_set(v___f_2614_, 6, v___y_2575_);
lean_closure_set(v___f_2614_, 7, v_b_2574_);
lean_closure_set(v___f_2614_, 8, v_a_2573_);
v___y_2583_ = v___f_2614_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2615_; uint8_t v_isInstance_2616_; 
v___x_2615_ = lean_array_fget_borrowed(v___x_2567_, v_a_2573_);
v_isInstance_2616_ = lean_ctor_get_uint8(v___x_2615_, sizeof(void*)*1 + 4);
if (v_isInstance_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___f_2620_; 
lean_inc(v___x_2608_);
v___x_2617_ = lean_box(v_usedLetOnly_2570_);
v___x_2618_ = lean_box(v_skipConstInApp_2571_);
v___x_2619_ = lean_box(v_skipInstances_2572_);
lean_inc(v_a_2573_);
lean_inc(v___y_2575_);
lean_inc_ref(v_post_2569_);
lean_inc_ref(v_pre_2568_);
v___f_2620_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2620_, 0, v_pre_2568_);
lean_closure_set(v___f_2620_, 1, v_post_2569_);
lean_closure_set(v___f_2620_, 2, v___x_2617_);
lean_closure_set(v___f_2620_, 3, v___x_2618_);
lean_closure_set(v___f_2620_, 4, v___x_2619_);
lean_closure_set(v___f_2620_, 5, v___x_2608_);
lean_closure_set(v___f_2620_, 6, v___y_2575_);
lean_closure_set(v___f_2620_, 7, v_b_2574_);
lean_closure_set(v___f_2620_, 8, v_a_2573_);
v___y_2583_ = v___f_2620_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2621_; lean_object* v___f_2622_; 
v___x_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2621_, 0, v_b_2574_);
v___f_2622_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2622_, 0, v___x_2621_);
v___y_2583_ = v___f_2622_;
goto v___jp_2582_;
}
}
}
v___jp_2582_:
{
lean_object* v___x_2584_; 
lean_inc(v___y_2580_);
lean_inc_ref(v___y_2579_);
lean_inc(v___y_2578_);
lean_inc_ref(v___y_2577_);
lean_inc(v___y_2576_);
v___x_2584_ = lean_apply_6(v___y_2583_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, lean_box(0));
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2597_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2597_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2597_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
if (lean_obj_tag(v_a_2585_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; 
lean_dec(v_a_2573_);
lean_dec_ref(v_post_2569_);
lean_dec_ref(v_pre_2568_);
v_a_2589_ = lean_ctor_get(v_a_2585_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v_a_2585_, 1);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 0, v_a_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_del_object(v___x_2587_);
v_a_2593_ = lean_ctor_get(v_a_2585_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v_a_2585_, 1);
v___x_2594_ = lean_unsigned_to_nat(1u);
v___x_2595_ = lean_nat_add(v_a_2573_, v___x_2594_);
lean_dec(v_a_2573_);
v_a_2573_ = v___x_2595_;
v_b_2574_ = v_a_2593_;
goto _start;
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v_a_2573_);
lean_dec_ref(v_post_2569_);
lean_dec_ref(v_pre_2568_);
v_a_2598_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2584_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2584_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2566_ = stack[0].m_obj;
lean_object* v___x_2567_ = stack[1].m_obj;
lean_object* v_pre_2568_ = stack[2].m_obj;
lean_object* v_post_2569_ = stack[3].m_obj;
uint8_t v_usedLetOnly_2570_ = stack[4].m_num;
uint8_t v_skipConstInApp_2571_ = stack[5].m_num;
uint8_t v_skipInstances_2572_ = stack[6].m_num;
lean_object* v_a_2573_ = stack[7].m_obj;
lean_object* v_b_2574_ = stack[8].m_obj;
lean_object* v___y_2575_ = stack[9].m_obj;
lean_object* v___y_2576_ = stack[10].m_obj;
lean_object* v___y_2577_ = stack[11].m_obj;
lean_object* v___y_2578_ = stack[12].m_obj;
lean_object* v___y_2579_ = stack[13].m_obj;
lean_object* v___y_2580_ = stack[14].m_obj;
lean_object* v_res_2623_;
v_res_2623_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_2566_, v___x_2567_, v_pre_2568_, v_post_2569_, v_usedLetOnly_2570_, v_skipConstInApp_2571_, v_skipInstances_2572_, v_a_2573_, v_b_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
stack->m_obj
 = v_res_2623_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t v_skipInstances_2624_, lean_object* v_pre_2625_, lean_object* v_post_2626_, uint8_t v_usedLetOnly_2627_, uint8_t v_skipConstInApp_2628_, lean_object* v_x_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_f_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; 
if (lean_obj_tag(v_x_2629_) == 5)
{
lean_object* v_fn_2689_; lean_object* v_arg_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_fn_2689_ = lean_ctor_get(v_x_2629_, 0);
lean_inc_ref(v_fn_2689_);
v_arg_2690_ = lean_ctor_get(v_x_2629_, 1);
lean_inc_ref(v_arg_2690_);
lean_dec_ref_known(v_x_2629_, 2);
v___x_2691_ = lean_array_set(v_x_2630_, v_x_2631_, v_arg_2690_);
v___x_2692_ = lean_unsigned_to_nat(1u);
v___x_2693_ = lean_nat_sub(v_x_2631_, v___x_2692_);
lean_dec(v_x_2631_);
v_x_2629_ = v_fn_2689_;
v_x_2630_ = v___x_2691_;
v_x_2631_ = v___x_2693_;
goto _start;
}
else
{
lean_dec(v_x_2631_);
if (v_skipConstInApp_2628_ == 0)
{
goto v___jp_2686_;
}
else
{
uint8_t v___x_2695_; 
v___x_2695_ = l_Lean_Expr_isConst(v_x_2629_);
if (v___x_2695_ == 0)
{
goto v___jp_2686_;
}
else
{
v_f_2640_ = v_x_2629_;
v___y_2641_ = v___y_2632_;
v___y_2642_ = v___y_2633_;
v___y_2643_ = v___y_2634_;
v___y_2644_ = v___y_2635_;
v___y_2645_ = v___y_2636_;
v___y_2646_ = v___y_2637_;
goto v___jp_2639_;
}
}
}
v___jp_2639_:
{
if (v_skipInstances_2624_ == 0)
{
size_t v_sz_2647_; size_t v___x_2648_; lean_object* v___x_2649_; 
v_sz_2647_ = lean_array_size(v_x_2630_);
v___x_2648_ = ((size_t)0ULL);
lean_inc_ref(v_post_2626_);
lean_inc_ref(v_pre_2625_);
v___x_2649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2625_, v_post_2626_, v_usedLetOnly_2627_, v_skipConstInApp_2628_, v_skipInstances_2624_, v_sz_2647_, v___x_2648_, v_x_2630_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
v___x_2651_ = l_Lean_mkAppN(v_f_2640_, v_a_2650_);
lean_dec(v_a_2650_);
v___x_2652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2625_, v_post_2626_, v_usedLetOnly_2627_, v_skipConstInApp_2628_, v_skipInstances_2624_, v___x_2651_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2652_;
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec_ref(v_f_2640_);
lean_dec_ref(v_post_2626_);
lean_dec_ref(v_pre_2625_);
v_a_2653_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2649_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2649_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = lean_array_get_size(v_x_2630_);
lean_inc_ref(v_f_2640_);
v___x_2662_ = l_Lean_Meta_getFunInfoNArgs(v_f_2640_, v___x_2661_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v_paramInfo_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
v_paramInfo_2664_ = lean_ctor_get(v_a_2663_, 0);
lean_inc_ref(v_paramInfo_2664_);
lean_dec(v_a_2663_);
v___x_2665_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2626_);
lean_inc_ref(v_pre_2625_);
v___x_2666_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_2661_, v_paramInfo_2664_, v_pre_2625_, v_post_2626_, v_usedLetOnly_2627_, v_skipConstInApp_2628_, v_skipInstances_2624_, v___x_2665_, v_x_2630_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec_ref(v_paramInfo_2664_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2666_, 1);
v___x_2668_ = l_Lean_mkAppN(v_f_2640_, v_a_2667_);
lean_dec(v_a_2667_);
v___x_2669_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2625_, v_post_2626_, v_usedLetOnly_2627_, v_skipConstInApp_2628_, v_skipInstances_2624_, v___x_2668_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2669_;
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec_ref(v_f_2640_);
lean_dec_ref(v_post_2626_);
lean_dec_ref(v_pre_2625_);
v_a_2670_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2666_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2666_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec_ref(v_f_2640_);
lean_dec_ref(v_x_2630_);
lean_dec_ref(v_post_2626_);
lean_dec_ref(v_pre_2625_);
v_a_2678_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2662_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2662_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
v___jp_2686_:
{
lean_object* v___x_2687_; 
lean_inc_ref(v_post_2626_);
lean_inc_ref(v_pre_2625_);
v___x_2687_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2625_, v_post_2626_, v_usedLetOnly_2627_, v_skipConstInApp_2628_, v_skipInstances_2624_, v_x_2629_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2687_, 1);
v_f_2640_ = v_a_2688_;
v___y_2641_ = v___y_2632_;
v___y_2642_ = v___y_2633_;
v___y_2643_ = v___y_2634_;
v___y_2644_ = v___y_2635_;
v___y_2645_ = v___y_2636_;
v___y_2646_ = v___y_2637_;
goto v___jp_2639_;
}
else
{
lean_dec_ref(v_x_2630_);
lean_dec_ref(v_post_2626_);
lean_dec_ref(v_pre_2625_);
return v___x_2687_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipInstances_2624_ = stack[0].m_num;
lean_object* v_pre_2625_ = stack[1].m_obj;
lean_object* v_post_2626_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2627_ = stack[3].m_num;
uint8_t v_skipConstInApp_2628_ = stack[4].m_num;
lean_object* v_x_2629_ = stack[5].m_obj;
lean_object* v_x_2630_ = stack[6].m_obj;
lean_object* v_x_2631_ = stack[7].m_obj;
lean_object* v___y_2632_ = stack[8].m_obj;
lean_object* v___y_2633_ = stack[9].m_obj;
lean_object* v___y_2634_ = stack[10].m_obj;
lean_object* v___y_2635_ = stack[11].m_obj;
lean_object* v___y_2636_ = stack[12].m_obj;
lean_object* v___y_2637_ = stack[13].m_obj;
lean_object* v_res_2696_;
v_res_2696_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2624_, v_pre_2625_, v_post_2626_, v_usedLetOnly_2627_, v_skipConstInApp_2628_, v_x_2629_, v_x_2630_, v_x_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
stack->m_obj
 = v_res_2696_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object* v___x_2697_, lean_object* v_pre_2698_, lean_object* v_e_2699_, lean_object* v_post_2700_, uint8_t v_usedLetOnly_2701_, uint8_t v_skipConstInApp_2702_, uint8_t v_skipInstances_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_Core_checkSystem(v___x_2697_, v___y_2708_, v___y_2709_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v___x_2712_; 
lean_dec_ref_known(v___x_2711_, 1);
lean_inc_ref(v_pre_2698_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
lean_inc(v___y_2705_);
lean_inc_ref(v_e_2699_);
v___x_2712_ = lean_apply_7(v_pre_2698_, v_e_2699_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, lean_box(0));
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2761_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2761_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2761_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___y_2718_; 
switch(lean_obj_tag(v_a_2713_))
{
case 0:
{
lean_object* v_e_2753_; lean_object* v___x_2755_; 
lean_dec_ref(v_post_2700_);
lean_dec_ref(v_e_2699_);
lean_dec_ref(v_pre_2698_);
v_e_2753_ = lean_ctor_get(v_a_2713_, 0);
lean_inc_ref(v_e_2753_);
lean_dec_ref_known(v_a_2713_, 1);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v_e_2753_);
v___x_2755_ = v___x_2715_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_e_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
case 1:
{
lean_object* v_e_2757_; lean_object* v___x_2758_; 
lean_del_object(v___x_2715_);
lean_dec_ref(v_e_2699_);
v_e_2757_ = lean_ctor_get(v_a_2713_, 0);
lean_inc_ref(v_e_2757_);
lean_dec_ref_known(v_a_2713_, 1);
v___x_2758_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v_e_2757_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2758_;
}
default: 
{
lean_object* v_e_x3f_2759_; 
lean_del_object(v___x_2715_);
v_e_x3f_2759_ = lean_ctor_get(v_a_2713_, 0);
lean_inc(v_e_x3f_2759_);
lean_dec_ref_known(v_a_2713_, 1);
if (lean_obj_tag(v_e_x3f_2759_) == 0)
{
v___y_2718_ = v_e_2699_;
goto v___jp_2717_;
}
else
{
lean_object* v_val_2760_; 
lean_dec_ref(v_e_2699_);
v_val_2760_ = lean_ctor_get(v_e_x3f_2759_, 0);
lean_inc(v_val_2760_);
lean_dec_ref_known(v_e_x3f_2759_, 1);
v___y_2718_ = v_val_2760_;
goto v___jp_2717_;
}
}
}
v___jp_2717_:
{
switch(lean_obj_tag(v___y_2718_))
{
case 7:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2720_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v___x_2719_, v___y_2718_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2720_;
}
case 6:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2722_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v___x_2721_, v___y_2718_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2722_;
}
case 8:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2724_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v___x_2723_, v___y_2718_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2724_;
}
case 5:
{
lean_object* v_dummy_2725_; lean_object* v_nargs_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_dummy_2725_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
v_nargs_2726_ = l_Lean_Expr_getAppNumArgs(v___y_2718_);
lean_inc(v_nargs_2726_);
v___x_2727_ = lean_mk_array(v_nargs_2726_, v_dummy_2725_);
v___x_2728_ = lean_unsigned_to_nat(1u);
v___x_2729_ = lean_nat_sub(v_nargs_2726_, v___x_2728_);
lean_dec(v_nargs_2726_);
v___x_2730_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2703_, v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v___y_2718_, v___x_2727_, v___x_2729_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2730_;
}
case 10:
{
lean_object* v_data_2731_; lean_object* v_expr_2732_; lean_object* v___x_2733_; 
v_data_2731_ = lean_ctor_get(v___y_2718_, 0);
v_expr_2732_ = lean_ctor_get(v___y_2718_, 1);
lean_inc_ref(v_expr_2732_);
lean_inc_ref(v_post_2700_);
lean_inc_ref(v_pre_2698_);
v___x_2733_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v_expr_2732_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; size_t v___x_2735_; size_t v___x_2736_; uint8_t v___x_2737_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2735_ = lean_ptr_addr(v_expr_2732_);
v___x_2736_ = lean_ptr_addr(v_a_2734_);
v___x_2737_ = lean_usize_dec_eq(v___x_2735_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_inc(v_data_2731_);
lean_dec_ref_known(v___y_2718_, 2);
v___x_2738_ = l_Lean_Expr_mdata___override(v_data_2731_, v_a_2734_);
v___x_2739_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v___x_2738_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2739_;
}
else
{
lean_object* v___x_2740_; 
lean_dec(v_a_2734_);
v___x_2740_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v___y_2718_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2740_;
}
}
else
{
lean_dec_ref_known(v___y_2718_, 2);
lean_dec_ref(v_post_2700_);
lean_dec_ref(v_pre_2698_);
return v___x_2733_;
}
}
case 11:
{
lean_object* v_typeName_2741_; lean_object* v_idx_2742_; lean_object* v_struct_2743_; lean_object* v___x_2744_; 
v_typeName_2741_ = lean_ctor_get(v___y_2718_, 0);
v_idx_2742_ = lean_ctor_get(v___y_2718_, 1);
v_struct_2743_ = lean_ctor_get(v___y_2718_, 2);
lean_inc_ref(v_struct_2743_);
lean_inc_ref(v_post_2700_);
lean_inc_ref(v_pre_2698_);
v___x_2744_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v_struct_2743_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; size_t v___x_2746_; size_t v___x_2747_; uint8_t v___x_2748_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
v___x_2746_ = lean_ptr_addr(v_struct_2743_);
v___x_2747_ = lean_ptr_addr(v_a_2745_);
v___x_2748_ = lean_usize_dec_eq(v___x_2746_, v___x_2747_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_inc(v_idx_2742_);
lean_inc(v_typeName_2741_);
lean_dec_ref_known(v___y_2718_, 3);
v___x_2749_ = l_Lean_Expr_proj___override(v_typeName_2741_, v_idx_2742_, v_a_2745_);
v___x_2750_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v___x_2749_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; 
lean_dec(v_a_2745_);
v___x_2751_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v___y_2718_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2751_;
}
}
else
{
lean_dec_ref_known(v___y_2718_, 3);
lean_dec_ref(v_post_2700_);
lean_dec_ref(v_pre_2698_);
return v___x_2744_;
}
}
default: 
{
lean_object* v___x_2752_; 
v___x_2752_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2698_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v___y_2718_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2752_;
}
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec_ref(v_post_2700_);
lean_dec_ref(v_e_2699_);
lean_dec_ref(v_pre_2698_);
v_a_2762_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2712_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2712_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec_ref(v_post_2700_);
lean_dec_ref(v_e_2699_);
lean_dec_ref(v_pre_2698_);
v_a_2770_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2711_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2711_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2697_ = stack[0].m_obj;
lean_object* v_pre_2698_ = stack[1].m_obj;
lean_object* v_e_2699_ = stack[2].m_obj;
lean_object* v_post_2700_ = stack[3].m_obj;
uint8_t v_usedLetOnly_2701_ = stack[4].m_num;
uint8_t v_skipConstInApp_2702_ = stack[5].m_num;
uint8_t v_skipInstances_2703_ = stack[6].m_num;
lean_object* v___y_2704_ = stack[7].m_obj;
lean_object* v___y_2705_ = stack[8].m_obj;
lean_object* v___y_2706_ = stack[9].m_obj;
lean_object* v___y_2707_ = stack[10].m_obj;
lean_object* v___y_2708_ = stack[11].m_obj;
lean_object* v___y_2709_ = stack[12].m_obj;
lean_object* v_res_2778_;
v_res_2778_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2697_, v_pre_2698_, v_e_2699_, v_post_2700_, v_usedLetOnly_2701_, v_skipConstInApp_2702_, v_skipInstances_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
stack->m_obj
 = v_res_2778_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2779_, lean_object* v_pre_2780_, lean_object* v_e_2781_, lean_object* v_post_2782_, lean_object* v_usedLetOnly_2783_, lean_object* v_skipConstInApp_2784_, lean_object* v_skipInstances_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
uint8_t v_usedLetOnly_boxed_2793_; uint8_t v_skipConstInApp_boxed_2794_; uint8_t v_skipInstances_boxed_2795_; lean_object* v_res_2796_; 
v_usedLetOnly_boxed_2793_ = lean_unbox(v_usedLetOnly_2783_);
v_skipConstInApp_boxed_2794_ = lean_unbox(v_skipConstInApp_2784_);
v_skipInstances_boxed_2795_ = lean_unbox(v_skipInstances_2785_);
v_res_2796_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2779_, v_pre_2780_, v_e_2781_, v_post_2782_, v_usedLetOnly_boxed_2793_, v_skipConstInApp_boxed_2794_, v_skipInstances_boxed_2795_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec(v___y_2786_);
return v_res_2796_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object* v_pre_2797_, lean_object* v_post_2798_, uint8_t v_usedLetOnly_2799_, uint8_t v_skipConstInApp_2800_, uint8_t v_skipInstances_2801_, lean_object* v_e_2802_, lean_object* v_a_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
lean_inc(v_a_2803_);
v___x_2810_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2810_, 0, lean_box(0));
lean_closure_set(v___x_2810_, 1, lean_box(0));
lean_closure_set(v___x_2810_, 2, v_a_2803_);
v___x_2811_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_2810_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2846_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2846_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2846_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_2812_, v_e_2802_);
lean_dec(v_a_2812_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___f_2821_; lean_object* v___x_2822_; 
lean_del_object(v___x_2814_);
v___x_2817_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0));
v___x_2818_ = lean_box(v_usedLetOnly_2799_);
v___x_2819_ = lean_box(v_skipConstInApp_2800_);
v___x_2820_ = lean_box(v_skipInstances_2801_);
lean_inc_ref(v_e_2802_);
v___f_2821_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed), 14, 7);
lean_closure_set(v___f_2821_, 0, v___x_2817_);
lean_closure_set(v___f_2821_, 1, v_pre_2797_);
lean_closure_set(v___f_2821_, 2, v_e_2802_);
lean_closure_set(v___f_2821_, 3, v_post_2798_);
lean_closure_set(v___f_2821_, 4, v___x_2818_);
lean_closure_set(v___f_2821_, 5, v___x_2819_);
lean_closure_set(v___f_2821_, 6, v___x_2820_);
v___x_2822_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_2821_, v_a_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___f_2824_; lean_object* v___x_2825_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc_n(v_a_2823_, 2);
lean_dec_ref_known(v___x_2822_, 1);
lean_inc(v_a_2803_);
v___f_2824_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2824_, 0, v_a_2803_);
lean_closure_set(v___f_2824_, 1, v_e_2802_);
lean_closure_set(v___f_2824_, 2, v_a_2823_);
v___x_2825_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_2824_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; 
v_unused_2833_ = lean_ctor_get(v___x_2825_, 0);
lean_dec(v_unused_2833_);
v___x_2827_ = v___x_2825_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_dec(v___x_2825_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v_a_2823_);
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2823_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2823_);
v_a_2834_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2825_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2825_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_dec_ref(v_e_2802_);
return v___x_2822_;
}
}
else
{
lean_object* v_val_2842_; lean_object* v___x_2844_; 
lean_dec_ref(v_e_2802_);
lean_dec_ref(v_post_2798_);
lean_dec_ref(v_pre_2797_);
v_val_2842_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_val_2842_);
lean_dec_ref_known(v___x_2816_, 1);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v_val_2842_);
v___x_2844_ = v___x_2814_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_val_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec_ref(v_e_2802_);
lean_dec_ref(v_post_2798_);
lean_dec_ref(v_pre_2797_);
v_a_2847_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2811_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2811_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2797_ = stack[0].m_obj;
lean_object* v_post_2798_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2799_ = stack[2].m_num;
uint8_t v_skipConstInApp_2800_ = stack[3].m_num;
uint8_t v_skipInstances_2801_ = stack[4].m_num;
lean_object* v_e_2802_ = stack[5].m_obj;
lean_object* v_a_2803_ = stack[6].m_obj;
lean_object* v___y_2804_ = stack[7].m_obj;
lean_object* v___y_2805_ = stack[8].m_obj;
lean_object* v___y_2806_ = stack[9].m_obj;
lean_object* v___y_2807_ = stack[10].m_obj;
lean_object* v___y_2808_ = stack[11].m_obj;
lean_object* v_res_2855_;
v_res_2855_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2797_, v_post_2798_, v_usedLetOnly_2799_, v_skipConstInApp_2800_, v_skipInstances_2801_, v_e_2802_, v_a_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
stack->m_obj
 = v_res_2855_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2856_, lean_object* v_post_2857_, uint8_t v_usedLetOnly_2858_, uint8_t v_skipConstInApp_2859_, uint8_t v_skipInstances_2860_, lean_object* v_fvars_2861_, lean_object* v_e_2862_, lean_object* v_a_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
if (lean_obj_tag(v_e_2862_) == 7)
{
lean_object* v_binderName_2870_; lean_object* v_binderType_2871_; lean_object* v_body_2872_; uint8_t v_binderInfo_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___f_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_binderName_2870_ = lean_ctor_get(v_e_2862_, 0);
lean_inc(v_binderName_2870_);
v_binderType_2871_ = lean_ctor_get(v_e_2862_, 1);
lean_inc_ref(v_binderType_2871_);
v_body_2872_ = lean_ctor_get(v_e_2862_, 2);
lean_inc_ref(v_body_2872_);
v_binderInfo_2873_ = lean_ctor_get_uint8(v_e_2862_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2862_, 3);
v___x_2874_ = lean_box(v_usedLetOnly_2858_);
v___x_2875_ = lean_box(v_skipConstInApp_2859_);
v___x_2876_ = lean_box(v_skipInstances_2860_);
lean_inc_ref(v_post_2857_);
lean_inc_ref(v_pre_2856_);
lean_inc_ref(v_fvars_2861_);
v___f_2877_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2877_, 0, v_fvars_2861_);
lean_closure_set(v___f_2877_, 1, v_pre_2856_);
lean_closure_set(v___f_2877_, 2, v_post_2857_);
lean_closure_set(v___f_2877_, 3, v___x_2874_);
lean_closure_set(v___f_2877_, 4, v___x_2875_);
lean_closure_set(v___f_2877_, 5, v___x_2876_);
lean_closure_set(v___f_2877_, 6, v_body_2872_);
v___x_2878_ = lean_expr_instantiate_rev(v_binderType_2871_, v_fvars_2861_);
lean_dec_ref(v_fvars_2861_);
lean_dec_ref(v_binderType_2871_);
v___x_2879_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2856_, v_post_2857_, v_usedLetOnly_2858_, v_skipConstInApp_2859_, v_skipInstances_2860_, v___x_2878_, v_a_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2879_, 1);
v___x_2881_ = 0;
v___x_2882_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2870_, v_binderInfo_2873_, v_a_2880_, v___f_2877_, v___x_2881_, v_a_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
return v___x_2882_;
}
else
{
lean_dec_ref(v___f_2877_);
lean_dec(v_binderName_2870_);
return v___x_2879_;
}
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = lean_expr_instantiate_rev(v_e_2862_, v_fvars_2861_);
lean_dec_ref(v_e_2862_);
lean_inc_ref(v_post_2857_);
lean_inc_ref(v_pre_2856_);
v___x_2884_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2856_, v_post_2857_, v_usedLetOnly_2858_, v_skipConstInApp_2859_, v_skipInstances_2860_, v___x_2883_, v_a_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; uint8_t v___x_2886_; uint8_t v___x_2887_; uint8_t v___x_2888_; lean_object* v___x_2889_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v___x_2886_ = 0;
v___x_2887_ = 1;
v___x_2888_ = 1;
v___x_2889_ = l_Lean_Meta_mkForallFVars(v_fvars_2861_, v_a_2885_, v___x_2886_, v_usedLetOnly_2858_, v___x_2887_, v___x_2888_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec_ref(v_fvars_2861_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2891_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2891_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2856_, v_post_2857_, v_usedLetOnly_2858_, v_skipConstInApp_2859_, v_skipInstances_2860_, v_a_2890_, v_a_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
return v___x_2891_;
}
else
{
lean_dec_ref(v_post_2857_);
lean_dec_ref(v_pre_2856_);
return v___x_2889_;
}
}
else
{
lean_dec_ref(v_fvars_2861_);
lean_dec_ref(v_post_2857_);
lean_dec_ref(v_pre_2856_);
return v___x_2884_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2856_ = stack[0].m_obj;
lean_object* v_post_2857_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2858_ = stack[2].m_num;
uint8_t v_skipConstInApp_2859_ = stack[3].m_num;
uint8_t v_skipInstances_2860_ = stack[4].m_num;
lean_object* v_fvars_2861_ = stack[5].m_obj;
lean_object* v_e_2862_ = stack[6].m_obj;
lean_object* v_a_2863_ = stack[7].m_obj;
lean_object* v___y_2864_ = stack[8].m_obj;
lean_object* v___y_2865_ = stack[9].m_obj;
lean_object* v___y_2866_ = stack[10].m_obj;
lean_object* v___y_2867_ = stack[11].m_obj;
lean_object* v___y_2868_ = stack[12].m_obj;
lean_object* v_res_2892_;
v_res_2892_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2856_, v_post_2857_, v_usedLetOnly_2858_, v_skipConstInApp_2859_, v_skipInstances_2860_, v_fvars_2861_, v_e_2862_, v_a_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
stack->m_obj
 = v_res_2892_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2893_, lean_object* v_pre_2894_, lean_object* v_post_2895_, uint8_t v_usedLetOnly_2896_, uint8_t v_skipConstInApp_2897_, uint8_t v_skipInstances_2898_, lean_object* v_body_2899_, lean_object* v_x_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = lean_array_push(v_fvars_2893_, v_x_2900_);
v___x_2909_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2894_, v_post_2895_, v_usedLetOnly_2896_, v_skipConstInApp_2897_, v_skipInstances_2898_, v___x_2908_, v_body_2899_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
return v___x_2909_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2893_ = stack[0].m_obj;
lean_object* v_pre_2894_ = stack[1].m_obj;
lean_object* v_post_2895_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2896_ = stack[3].m_num;
uint8_t v_skipConstInApp_2897_ = stack[4].m_num;
uint8_t v_skipInstances_2898_ = stack[5].m_num;
lean_object* v_body_2899_ = stack[6].m_obj;
lean_object* v_x_2900_ = stack[7].m_obj;
lean_object* v___y_2901_ = stack[8].m_obj;
lean_object* v___y_2902_ = stack[9].m_obj;
lean_object* v___y_2903_ = stack[10].m_obj;
lean_object* v___y_2904_ = stack[11].m_obj;
lean_object* v___y_2905_ = stack[12].m_obj;
lean_object* v___y_2906_ = stack[13].m_obj;
lean_object* v_res_2910_;
v_res_2910_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2893_, v_pre_2894_, v_post_2895_, v_usedLetOnly_2896_, v_skipConstInApp_2897_, v_skipInstances_2898_, v_body_2899_, v_x_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
stack->m_obj
 = v_res_2910_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2911_, lean_object* v_post_2912_, lean_object* v_usedLetOnly_2913_, lean_object* v_skipConstInApp_2914_, lean_object* v_skipInstances_2915_, lean_object* v_e_2916_, lean_object* v_a_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
uint8_t v_usedLetOnly_boxed_2924_; uint8_t v_skipConstInApp_boxed_2925_; uint8_t v_skipInstances_boxed_2926_; lean_object* v_res_2927_; 
v_usedLetOnly_boxed_2924_ = lean_unbox(v_usedLetOnly_2913_);
v_skipConstInApp_boxed_2925_ = lean_unbox(v_skipConstInApp_2914_);
v_skipInstances_boxed_2926_ = lean_unbox(v_skipInstances_2915_);
v_res_2927_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2911_, v_post_2912_, v_usedLetOnly_boxed_2924_, v_skipConstInApp_boxed_2925_, v_skipInstances_boxed_2926_, v_e_2916_, v_a_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec(v_a_2917_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2928_, lean_object* v_post_2929_, lean_object* v_usedLetOnly_2930_, lean_object* v_skipConstInApp_2931_, lean_object* v_skipInstances_2932_, lean_object* v_sz_2933_, lean_object* v_i_2934_, lean_object* v_bs_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
uint8_t v_usedLetOnly_boxed_2943_; uint8_t v_skipConstInApp_boxed_2944_; uint8_t v_skipInstances_boxed_2945_; size_t v_sz_boxed_2946_; size_t v_i_boxed_2947_; lean_object* v_res_2948_; 
v_usedLetOnly_boxed_2943_ = lean_unbox(v_usedLetOnly_2930_);
v_skipConstInApp_boxed_2944_ = lean_unbox(v_skipConstInApp_2931_);
v_skipInstances_boxed_2945_ = lean_unbox(v_skipInstances_2932_);
v_sz_boxed_2946_ = lean_unbox_usize(v_sz_2933_);
lean_dec(v_sz_2933_);
v_i_boxed_2947_ = lean_unbox_usize(v_i_2934_);
lean_dec(v_i_2934_);
v_res_2948_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2928_, v_post_2929_, v_usedLetOnly_boxed_2943_, v_skipConstInApp_boxed_2944_, v_skipInstances_boxed_2945_, v_sz_boxed_2946_, v_i_boxed_2947_, v_bs_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec(v___y_2936_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_2949_, lean_object* v_post_2950_, lean_object* v_usedLetOnly_2951_, lean_object* v_skipConstInApp_2952_, lean_object* v_skipInstances_2953_, lean_object* v_e_2954_, lean_object* v_a_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
uint8_t v_usedLetOnly_boxed_2962_; uint8_t v_skipConstInApp_boxed_2963_; uint8_t v_skipInstances_boxed_2964_; lean_object* v_res_2965_; 
v_usedLetOnly_boxed_2962_ = lean_unbox(v_usedLetOnly_2951_);
v_skipConstInApp_boxed_2963_ = lean_unbox(v_skipConstInApp_2952_);
v_skipInstances_boxed_2964_ = lean_unbox(v_skipInstances_2953_);
v_res_2965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2949_, v_post_2950_, v_usedLetOnly_boxed_2962_, v_skipConstInApp_boxed_2963_, v_skipInstances_boxed_2964_, v_e_2954_, v_a_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec(v_a_2955_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_2966_, lean_object* v_post_2967_, lean_object* v_usedLetOnly_2968_, lean_object* v_skipConstInApp_2969_, lean_object* v_skipInstances_2970_, lean_object* v_fvars_2971_, lean_object* v_e_2972_, lean_object* v_a_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
uint8_t v_usedLetOnly_boxed_2980_; uint8_t v_skipConstInApp_boxed_2981_; uint8_t v_skipInstances_boxed_2982_; lean_object* v_res_2983_; 
v_usedLetOnly_boxed_2980_ = lean_unbox(v_usedLetOnly_2968_);
v_skipConstInApp_boxed_2981_ = lean_unbox(v_skipConstInApp_2969_);
v_skipInstances_boxed_2982_ = lean_unbox(v_skipInstances_2970_);
v_res_2983_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2966_, v_post_2967_, v_usedLetOnly_boxed_2980_, v_skipConstInApp_boxed_2981_, v_skipInstances_boxed_2982_, v_fvars_2971_, v_e_2972_, v_a_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec(v_a_2973_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_2984_, lean_object* v_post_2985_, lean_object* v_usedLetOnly_2986_, lean_object* v_skipConstInApp_2987_, lean_object* v_skipInstances_2988_, lean_object* v_fvars_2989_, lean_object* v_e_2990_, lean_object* v_a_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
uint8_t v_usedLetOnly_boxed_2998_; uint8_t v_skipConstInApp_boxed_2999_; uint8_t v_skipInstances_boxed_3000_; lean_object* v_res_3001_; 
v_usedLetOnly_boxed_2998_ = lean_unbox(v_usedLetOnly_2986_);
v_skipConstInApp_boxed_2999_ = lean_unbox(v_skipConstInApp_2987_);
v_skipInstances_boxed_3000_ = lean_unbox(v_skipInstances_2988_);
v_res_3001_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2984_, v_post_2985_, v_usedLetOnly_boxed_2998_, v_skipConstInApp_boxed_2999_, v_skipInstances_boxed_3000_, v_fvars_2989_, v_e_2990_, v_a_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v_a_2991_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_3002_, lean_object* v_post_3003_, lean_object* v_usedLetOnly_3004_, lean_object* v_skipConstInApp_3005_, lean_object* v_skipInstances_3006_, lean_object* v_fvars_3007_, lean_object* v_e_3008_, lean_object* v_a_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
uint8_t v_usedLetOnly_boxed_3016_; uint8_t v_skipConstInApp_boxed_3017_; uint8_t v_skipInstances_boxed_3018_; lean_object* v_res_3019_; 
v_usedLetOnly_boxed_3016_ = lean_unbox(v_usedLetOnly_3004_);
v_skipConstInApp_boxed_3017_ = lean_unbox(v_skipConstInApp_3005_);
v_skipInstances_boxed_3018_ = lean_unbox(v_skipInstances_3006_);
v_res_3019_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_3002_, v_post_3003_, v_usedLetOnly_boxed_3016_, v_skipConstInApp_boxed_3017_, v_skipInstances_boxed_3018_, v_fvars_3007_, v_e_3008_, v_a_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec(v_a_3009_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_3020_, lean_object* v___x_3021_, lean_object* v_pre_3022_, lean_object* v_post_3023_, lean_object* v_usedLetOnly_3024_, lean_object* v_skipConstInApp_3025_, lean_object* v_skipInstances_3026_, lean_object* v_a_3027_, lean_object* v_b_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
uint8_t v_usedLetOnly_boxed_3036_; uint8_t v_skipConstInApp_boxed_3037_; uint8_t v_skipInstances_boxed_3038_; lean_object* v_res_3039_; 
v_usedLetOnly_boxed_3036_ = lean_unbox(v_usedLetOnly_3024_);
v_skipConstInApp_boxed_3037_ = lean_unbox(v_skipConstInApp_3025_);
v_skipInstances_boxed_3038_ = lean_unbox(v_skipInstances_3026_);
v_res_3039_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3020_, v___x_3021_, v_pre_3022_, v_post_3023_, v_usedLetOnly_boxed_3036_, v_skipConstInApp_boxed_3037_, v_skipInstances_boxed_3038_, v_a_3027_, v_b_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___x_3021_);
lean_dec(v_upperBound_3020_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_3040_, lean_object* v_pre_3041_, lean_object* v_post_3042_, lean_object* v_usedLetOnly_3043_, lean_object* v_skipConstInApp_3044_, lean_object* v_x_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
uint8_t v_skipInstances_boxed_3055_; uint8_t v_usedLetOnly_boxed_3056_; uint8_t v_skipConstInApp_boxed_3057_; lean_object* v_res_3058_; 
v_skipInstances_boxed_3055_ = lean_unbox(v_skipInstances_3040_);
v_usedLetOnly_boxed_3056_ = lean_unbox(v_usedLetOnly_3043_);
v_skipConstInApp_boxed_3057_ = lean_unbox(v_skipConstInApp_3044_);
v_res_3058_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_3055_, v_pre_3041_, v_post_3042_, v_usedLetOnly_boxed_3056_, v_skipConstInApp_boxed_3057_, v_x_3045_, v_x_3046_, v_x_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec(v___y_3048_);
return v_res_3058_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_3059_, lean_object* v_x_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = lean_apply_1(v_x_3060_, lean_box(0));
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3060_ = stack[1].m_obj;
lean_object* v___y_3061_ = stack[2].m_obj;
lean_object* v___y_3062_ = stack[3].m_obj;
lean_object* v___y_3063_ = stack[4].m_obj;
lean_object* v___y_3064_ = stack[5].m_obj;
lean_object* v___y_3065_ = stack[6].m_obj;
lean_object* v_res_3069_;
v_res_3069_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v_x_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
stack->m_obj
 = v_res_3069_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3070_, lean_object* v_x_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_3070_, v_x_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
return v_res_3078_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = lean_box(0);
v___x_3080_ = lean_unsigned_to_nat(16u);
v___x_3081_ = lean_mk_array(v___x_3080_, v___x_3079_);
return v___x_3081_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3082_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
lean_ctor_set(v___x_3084_, 1, v___x_3082_);
return v___x_3084_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3086_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3086_, 0, lean_box(0));
lean_closure_set(v___x_3086_, 1, lean_box(0));
lean_closure_set(v___x_3086_, 2, v___x_3085_);
return v___x_3086_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3087_, lean_object* v_pre_3088_, lean_object* v_post_3089_, uint8_t v_usedLetOnly_3090_, uint8_t v_skipConstInApp_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
uint8_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v_a_3101_; lean_object* v___x_3102_; 
v___x_3098_ = 0;
v___x_3099_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3100_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3099_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref(v___x_3100_);
v___x_3102_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3088_, v_post_3089_, v_usedLetOnly_3090_, v_skipConstInApp_3091_, v___x_3098_, v_input_3087_, v_a_3101_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
v___x_3104_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3104_, 0, lean_box(0));
lean_closure_set(v___x_3104_, 1, lean_box(0));
lean_closure_set(v___x_3104_, 2, v_a_3101_);
v___x_3105_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3104_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3112_ == 0)
{
lean_object* v_unused_3113_; 
v_unused_3113_ = lean_ctor_get(v___x_3105_, 0);
lean_dec(v_unused_3113_);
v___x_3107_ = v___x_3105_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_dec(v___x_3105_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v_a_3103_);
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3103_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
else
{
lean_dec(v_a_3101_);
return v___x_3102_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_3087_ = stack[0].m_obj;
lean_object* v_pre_3088_ = stack[1].m_obj;
lean_object* v_post_3089_ = stack[2].m_obj;
uint8_t v_usedLetOnly_3090_ = stack[3].m_num;
uint8_t v_skipConstInApp_3091_ = stack[4].m_num;
lean_object* v___y_3092_ = stack[5].m_obj;
lean_object* v___y_3093_ = stack[6].m_obj;
lean_object* v___y_3094_ = stack[7].m_obj;
lean_object* v___y_3095_ = stack[8].m_obj;
lean_object* v___y_3096_ = stack[9].m_obj;
lean_object* v_res_3114_;
v_res_3114_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3087_, v_pre_3088_, v_post_3089_, v_usedLetOnly_3090_, v_skipConstInApp_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
stack->m_obj
 = v_res_3114_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3115_, lean_object* v_pre_3116_, lean_object* v_post_3117_, lean_object* v_usedLetOnly_3118_, lean_object* v_skipConstInApp_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
uint8_t v_usedLetOnly_boxed_3126_; uint8_t v_skipConstInApp_boxed_3127_; lean_object* v_res_3128_; 
v_usedLetOnly_boxed_3126_ = lean_unbox(v_usedLetOnly_3118_);
v_skipConstInApp_boxed_3127_ = lean_unbox(v_skipConstInApp_3119_);
v_res_3128_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3115_, v_pre_3116_, v_post_3117_, v_usedLetOnly_boxed_3126_, v_skipConstInApp_boxed_3127_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
return v_res_3128_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3130_, uint8_t v_elimTrivial_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v___x_3137_; lean_object* v_pre_3138_; lean_object* v___f_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3137_ = lean_box(v_elimTrivial_3131_);
v_pre_3138_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3138_, 0, v___x_3137_);
v___f_3139_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0));
v___x_3140_ = 0;
v___x_3141_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_3142_ = lean_st_mk_ref(v___x_3141_);
v___x_3143_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3130_, v_pre_3138_, v___f_3139_, v___x_3140_, v___x_3140_, v___x_3142_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3152_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3146_ = v___x_3143_;
v_isShared_3147_ = v_isSharedCheck_3152_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3152_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; lean_object* v___x_3150_; 
v___x_3148_ = lean_st_ref_get(v___x_3142_);
lean_dec(v___x_3142_);
lean_dec(v___x_3148_);
if (v_isShared_3147_ == 0)
{
v___x_3150_ = v___x_3146_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3144_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
else
{
lean_dec(v___x_3142_);
return v___x_3143_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elimLetsCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3130_ = stack[0].m_obj;
uint8_t v_elimTrivial_3131_ = stack[1].m_num;
lean_object* v_a_3132_ = stack[2].m_obj;
lean_object* v_a_3133_ = stack[3].m_obj;
lean_object* v_a_3134_ = stack[4].m_obj;
lean_object* v_a_3135_ = stack[5].m_obj;
lean_object* v_res_3153_;
v_res_3153_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3130_, v_elimTrivial_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
stack->m_obj
 = v_res_3153_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3154_, lean_object* v_elimTrivial_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
uint8_t v_elimTrivial_boxed_3161_; lean_object* v_res_3162_; 
v_elimTrivial_boxed_3161_ = lean_unbox(v_elimTrivial_3155_);
v_res_3162_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3154_, v_elimTrivial_boxed_3161_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
return v_res_3162_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_upperBound_3163_, lean_object* v___x_3164_, lean_object* v_pre_3165_, lean_object* v_post_3166_, uint8_t v_usedLetOnly_3167_, uint8_t v_skipConstInApp_3168_, uint8_t v_skipInstances_3169_, lean_object* v___x_3170_, lean_object* v_inst_3171_, lean_object* v_R_3172_, lean_object* v_a_3173_, lean_object* v_b_3174_, lean_object* v_c_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; 
v___x_3183_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3163_, v___x_3164_, v_pre_3165_, v_post_3166_, v_usedLetOnly_3167_, v_skipConstInApp_3168_, v_skipInstances_3169_, v_a_3173_, v_b_3174_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
return v___x_3183_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3163_ = stack[0].m_obj;
lean_object* v___x_3164_ = stack[1].m_obj;
lean_object* v_pre_3165_ = stack[2].m_obj;
lean_object* v_post_3166_ = stack[3].m_obj;
uint8_t v_usedLetOnly_3167_ = stack[4].m_num;
uint8_t v_skipConstInApp_3168_ = stack[5].m_num;
uint8_t v_skipInstances_3169_ = stack[6].m_num;
lean_object* v___x_3170_ = stack[7].m_obj;
lean_object* v_a_3173_ = stack[10].m_obj;
lean_object* v_b_3174_ = stack[11].m_obj;
lean_object* v___y_3176_ = stack[13].m_obj;
lean_object* v___y_3177_ = stack[14].m_obj;
lean_object* v___y_3178_ = stack[15].m_obj;
lean_object* v___y_3179_ = stack[16].m_obj;
lean_object* v___y_3180_ = stack[17].m_obj;
lean_object* v___y_3181_ = stack[18].m_obj;
lean_object* v_res_3184_;
v_res_3184_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3163_, v___x_3164_, v_pre_3165_, v_post_3166_, v_usedLetOnly_3167_, v_skipConstInApp_3168_, v_skipInstances_3169_, v___x_3170_, lean_box(0), lean_box(0), v_a_3173_, v_b_3174_, lean_box(0), v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
stack->m_obj
 = v_res_3184_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3185_ = _args[0];
lean_object* v___x_3186_ = _args[1];
lean_object* v_pre_3187_ = _args[2];
lean_object* v_post_3188_ = _args[3];
lean_object* v_usedLetOnly_3189_ = _args[4];
lean_object* v_skipConstInApp_3190_ = _args[5];
lean_object* v_skipInstances_3191_ = _args[6];
lean_object* v___x_3192_ = _args[7];
lean_object* v_inst_3193_ = _args[8];
lean_object* v_R_3194_ = _args[9];
lean_object* v_a_3195_ = _args[10];
lean_object* v_b_3196_ = _args[11];
lean_object* v_c_3197_ = _args[12];
lean_object* v___y_3198_ = _args[13];
lean_object* v___y_3199_ = _args[14];
lean_object* v___y_3200_ = _args[15];
lean_object* v___y_3201_ = _args[16];
lean_object* v___y_3202_ = _args[17];
lean_object* v___y_3203_ = _args[18];
lean_object* v___y_3204_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3205_; uint8_t v_skipConstInApp_boxed_3206_; uint8_t v_skipInstances_boxed_3207_; lean_object* v_res_3208_; 
v_usedLetOnly_boxed_3205_ = lean_unbox(v_usedLetOnly_3189_);
v_skipConstInApp_boxed_3206_ = lean_unbox(v_skipConstInApp_3190_);
v_skipInstances_boxed_3207_ = lean_unbox(v_skipInstances_3191_);
v_res_3208_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3185_, v___x_3186_, v_pre_3187_, v_post_3188_, v_usedLetOnly_boxed_3205_, v_skipConstInApp_boxed_3206_, v_skipInstances_boxed_3207_, v___x_3192_, v_inst_3193_, v_R_3194_, v_a_3195_, v_b_3196_, v_c_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec(v___x_3192_);
lean_dec_ref(v___x_3186_);
lean_dec(v_upperBound_3185_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3209_, lean_object* v_m_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_3210_, v_a_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_3213_, lean_object* v_m_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_3213_, v_m_3214_, v_a_3215_);
lean_dec_ref(v_a_3215_);
lean_dec_ref(v_m_3214_);
return v_res_3216_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3217_, lean_object* v_name_3218_, uint8_t v_bi_3219_, lean_object* v_type_3220_, lean_object* v_k_3221_, uint8_t v_kind_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3218_, v_bi_3219_, v_type_3220_, v_k_3221_, v_kind_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
return v___x_3230_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3218_ = stack[1].m_obj;
uint8_t v_bi_3219_ = stack[2].m_num;
lean_object* v_type_3220_ = stack[3].m_obj;
lean_object* v_k_3221_ = stack[4].m_obj;
uint8_t v_kind_3222_ = stack[5].m_num;
lean_object* v___y_3223_ = stack[6].m_obj;
lean_object* v___y_3224_ = stack[7].m_obj;
lean_object* v___y_3225_ = stack[8].m_obj;
lean_object* v___y_3226_ = stack[9].m_obj;
lean_object* v___y_3227_ = stack[10].m_obj;
lean_object* v___y_3228_ = stack[11].m_obj;
lean_object* v_res_3231_;
v_res_3231_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_box(0), v_name_3218_, v_bi_3219_, v_type_3220_, v_k_3221_, v_kind_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
stack->m_obj
 = v_res_3231_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3232_, lean_object* v_name_3233_, lean_object* v_bi_3234_, lean_object* v_type_3235_, lean_object* v_k_3236_, lean_object* v_kind_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
uint8_t v_bi_boxed_3245_; uint8_t v_kind_boxed_3246_; lean_object* v_res_3247_; 
v_bi_boxed_3245_ = lean_unbox(v_bi_3234_);
v_kind_boxed_3246_ = lean_unbox(v_kind_3237_);
v_res_3247_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3232_, v_name_3233_, v_bi_boxed_3245_, v_type_3235_, v_k_3236_, v_kind_boxed_3246_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec(v___y_3238_);
return v_res_3247_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3248_, lean_object* v_name_3249_, lean_object* v_type_3250_, lean_object* v_val_3251_, lean_object* v_k_3252_, uint8_t v_nondep_3253_, uint8_t v_kind_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3249_, v_type_3250_, v_val_3251_, v_k_3252_, v_nondep_3253_, v_kind_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
return v___x_3262_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3249_ = stack[1].m_obj;
lean_object* v_type_3250_ = stack[2].m_obj;
lean_object* v_val_3251_ = stack[3].m_obj;
lean_object* v_k_3252_ = stack[4].m_obj;
uint8_t v_nondep_3253_ = stack[5].m_num;
uint8_t v_kind_3254_ = stack[6].m_num;
lean_object* v___y_3255_ = stack[7].m_obj;
lean_object* v___y_3256_ = stack[8].m_obj;
lean_object* v___y_3257_ = stack[9].m_obj;
lean_object* v___y_3258_ = stack[10].m_obj;
lean_object* v___y_3259_ = stack[11].m_obj;
lean_object* v___y_3260_ = stack[12].m_obj;
lean_object* v_res_3263_;
v_res_3263_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_box(0), v_name_3249_, v_type_3250_, v_val_3251_, v_k_3252_, v_nondep_3253_, v_kind_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
stack->m_obj
 = v_res_3263_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3264_, lean_object* v_name_3265_, lean_object* v_type_3266_, lean_object* v_val_3267_, lean_object* v_k_3268_, lean_object* v_nondep_3269_, lean_object* v_kind_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
uint8_t v_nondep_boxed_3278_; uint8_t v_kind_boxed_3279_; lean_object* v_res_3280_; 
v_nondep_boxed_3278_ = lean_unbox(v_nondep_3269_);
v_kind_boxed_3279_ = lean_unbox(v_kind_3270_);
v_res_3280_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3264_, v_name_3265_, v_type_3266_, v_val_3267_, v_k_3268_, v_nondep_boxed_3278_, v_kind_boxed_3279_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec(v___y_3271_);
return v_res_3280_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3281_, lean_object* v_ref_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3282_);
return v___x_3288_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3282_ = stack[1].m_obj;
lean_object* v___y_3283_ = stack[2].m_obj;
lean_object* v___y_3284_ = stack[3].m_obj;
lean_object* v___y_3285_ = stack[4].m_obj;
lean_object* v___y_3286_ = stack[5].m_obj;
lean_object* v_res_3289_;
v_res_3289_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_box(0), v_ref_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
stack->m_obj
 = v_res_3289_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3290_, lean_object* v_ref_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3290_, v_ref_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
return v_res_3297_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3298_, lean_object* v_x_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3299_ = stack[1].m_obj;
lean_object* v___y_3300_ = stack[2].m_obj;
lean_object* v___y_3301_ = stack[3].m_obj;
lean_object* v___y_3302_ = stack[4].m_obj;
lean_object* v___y_3303_ = stack[5].m_obj;
lean_object* v___y_3304_ = stack[6].m_obj;
lean_object* v___y_3305_ = stack[7].m_obj;
lean_object* v_res_3308_;
v_res_3308_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_box(0), v_x_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
stack->m_obj
 = v_res_3308_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3309_, lean_object* v_x_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3309_, v_x_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec(v___y_3311_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3319_, lean_object* v_m_3320_, lean_object* v_a_3321_, lean_object* v_b_3322_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3320_, v_a_3321_, v_b_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_3324_, lean_object* v_a_3325_, lean_object* v_x_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_3325_, v_x_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3328_, lean_object* v_a_3329_, lean_object* v_x_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_3328_, v_a_3329_, v_x_3330_);
lean_dec(v_x_3330_);
lean_dec_ref(v_a_3329_);
return v_res_3331_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3332_, lean_object* v_a_3333_, lean_object* v_x_3334_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_3333_, v_x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3333_ = stack[1].m_obj;
lean_object* v_x_3334_ = stack[2].m_obj;
uint8_t v_res_3336_;
v_res_3336_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_box(0), v_a_3333_, v_x_3334_);
stack->m_num = v_res_3336_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3337_, lean_object* v_a_3338_, lean_object* v_x_3339_){
_start:
{
uint8_t v_res_3340_; lean_object* v_r_3341_; 
v_res_3340_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3337_, v_a_3338_, v_x_3339_);
lean_dec(v_x_3339_);
lean_dec_ref(v_a_3338_);
v_r_3341_ = lean_box(v_res_3340_);
return v_r_3341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_3342_, lean_object* v_data_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_3345_, lean_object* v_a_3346_, lean_object* v_b_3347_, lean_object* v_x_3348_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_3346_, v_b_3347_, v_x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_3350_, lean_object* v_i_3351_, lean_object* v_source_3352_, lean_object* v_target_3353_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_3351_, v_source_3352_, v_target_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_3355_, lean_object* v_x_3356_, lean_object* v_x_3357_){
_start:
{
lean_object* v___x_3358_; 
v___x_3358_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3356_, v_x_3357_);
return v___x_3358_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3359_, lean_object* v_x_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3359_, v_x_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3366_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
v_a_3375_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3366_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3366_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3359_ = stack[0].m_obj;
lean_object* v_x_3360_ = stack[1].m_obj;
lean_object* v___y_3361_ = stack[2].m_obj;
lean_object* v___y_3362_ = stack[3].m_obj;
lean_object* v___y_3363_ = stack[4].m_obj;
lean_object* v___y_3364_ = stack[5].m_obj;
lean_object* v_res_3383_;
v_res_3383_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3359_, v_x_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
stack->m_obj
 = v_res_3383_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3384_, lean_object* v_x_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3384_, v_x_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
return v_res_3391_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3392_, lean_object* v_mvarId_3393_, lean_object* v_x_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3393_, v_x_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
return v___x_3400_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3393_ = stack[1].m_obj;
lean_object* v_x_3394_ = stack[2].m_obj;
lean_object* v___y_3395_ = stack[3].m_obj;
lean_object* v___y_3396_ = stack[4].m_obj;
lean_object* v___y_3397_ = stack[5].m_obj;
lean_object* v___y_3398_ = stack[6].m_obj;
lean_object* v_res_3401_;
v_res_3401_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_box(0), v_mvarId_3393_, v_x_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
stack->m_obj
 = v_res_3401_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3402_, lean_object* v_mvarId_3403_, lean_object* v_x_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3402_, v_mvarId_3403_, v_x_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
return v_res_3410_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3411_, lean_object* v_as_3412_, size_t v_sz_3413_, size_t v_i_3414_, lean_object* v_b_3415_){
_start:
{
uint8_t v___x_3417_; 
v___x_3417_ = lean_usize_dec_lt(v_i_3414_, v_sz_3413_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3418_, 0, v_b_3415_);
return v___x_3418_;
}
else
{
lean_object* v_snd_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3466_; 
v_snd_3419_ = lean_ctor_get(v_b_3415_, 1);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_b_3415_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; 
v_unused_3467_ = lean_ctor_get(v_b_3415_, 0);
lean_dec(v_unused_3467_);
v___x_3421_ = v_b_3415_;
v_isShared_3422_ = v_isSharedCheck_3466_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_snd_3419_);
lean_dec(v_b_3415_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3466_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; lean_object* v_a_3425_; lean_object* v_a_3432_; 
v___x_3423_ = lean_box(0);
v_a_3432_ = lean_array_uget_borrowed(v_as_3412_, v_i_3414_);
if (lean_obj_tag(v_a_3432_) == 0)
{
v_a_3425_ = v_snd_3419_;
goto v___jp_3424_;
}
else
{
lean_object* v_val_3433_; lean_object* v_fst_3434_; lean_object* v_snd_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3465_; 
v_val_3433_ = lean_ctor_get(v_a_3432_, 0);
v_fst_3434_ = lean_ctor_get(v_snd_3419_, 0);
v_snd_3435_ = lean_ctor_get(v_snd_3419_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_snd_3419_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3437_ = v_snd_3419_;
v_isShared_3438_ = v_isSharedCheck_3465_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_snd_3435_);
lean_inc(v_fst_3434_);
lean_dec(v_snd_3419_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3465_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
uint8_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = 0;
v___x_3440_ = l_Lean_LocalDecl_value_x3f(v_val_3433_, v___x_3439_);
if (lean_obj_tag(v___x_3440_) == 1)
{
lean_object* v_val_3441_; lean_object* v___x_3442_; 
v_val_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_val_3441_);
lean_dec_ref_known(v___x_3440_, 1);
v___x_3442_ = l_Lean_LocalDecl_type(v_val_3433_);
if (lean_obj_tag(v___x_3442_) == 10)
{
lean_object* v_data_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; uint8_t v___x_3448_; 
v_data_3443_ = lean_ctor_get(v___x_3442_, 0);
lean_inc(v_data_3443_);
lean_dec_ref_known(v___x_3442_, 2);
v___x_3444_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3445_ = lean_unsigned_to_nat(2u);
v___x_3446_ = l_Lean_KVMap_getNat(v_data_3443_, v___x_3444_, v___x_3445_);
lean_dec(v_data_3443_);
v___x_3447_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3446_);
lean_dec(v___x_3446_);
v___x_3448_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3447_, v_val_3441_, v_elimTrivial_3411_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3449_ = l_Lean_LocalDecl_fvarId(v_val_3433_);
v___x_3450_ = l_Lean_mkFVar(v___x_3449_);
v___x_3451_ = lean_array_push(v_fst_3434_, v___x_3450_);
v___x_3452_ = lean_array_push(v_snd_3435_, v_val_3441_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 1, v___x_3452_);
lean_ctor_set(v___x_3437_, 0, v___x_3451_);
v___x_3454_ = v___x_3437_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
v_a_3425_ = v___x_3454_;
goto v___jp_3424_;
}
}
else
{
lean_object* v___x_3457_; 
lean_dec(v_val_3441_);
if (v_isShared_3438_ == 0)
{
v___x_3457_ = v___x_3437_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_fst_3434_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_snd_3435_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
v_a_3425_ = v___x_3457_;
goto v___jp_3424_;
}
}
}
else
{
lean_object* v___x_3460_; 
lean_dec_ref(v___x_3442_);
lean_dec(v_val_3441_);
if (v_isShared_3438_ == 0)
{
v___x_3460_ = v___x_3437_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_fst_3434_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_snd_3435_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
v_a_3425_ = v___x_3460_;
goto v___jp_3424_;
}
}
}
else
{
lean_object* v___x_3463_; 
lean_dec(v___x_3440_);
if (v_isShared_3438_ == 0)
{
v___x_3463_ = v___x_3437_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_fst_3434_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_snd_3435_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
v_a_3425_ = v___x_3463_;
goto v___jp_3424_;
}
}
}
}
v___jp_3424_:
{
lean_object* v___x_3427_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 1, v_a_3425_);
lean_ctor_set(v___x_3421_, 0, v___x_3423_);
v___x_3427_ = v___x_3421_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_a_3425_);
v___x_3427_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
size_t v___x_3428_; size_t v___x_3429_; 
v___x_3428_ = ((size_t)1ULL);
v___x_3429_ = lean_usize_add(v_i_3414_, v___x_3428_);
v_i_3414_ = v___x_3429_;
v_b_3415_ = v___x_3427_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_elimTrivial_3411_ = stack[0].m_num;
lean_object* v_as_3412_ = stack[1].m_obj;
size_t v_sz_3413_ = stack[2].m_num;
size_t v_i_3414_ = stack[3].m_num;
lean_object* v_b_3415_ = stack[4].m_obj;
lean_object* v_res_3468_;
v_res_3468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3411_, v_as_3412_, v_sz_3413_, v_i_3414_, v_b_3415_);
stack->m_obj
 = v_res_3468_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3469_, lean_object* v_as_3470_, lean_object* v_sz_3471_, lean_object* v_i_3472_, lean_object* v_b_3473_, lean_object* v___y_3474_){
_start:
{
uint8_t v_elimTrivial_boxed_3475_; size_t v_sz_boxed_3476_; size_t v_i_boxed_3477_; lean_object* v_res_3478_; 
v_elimTrivial_boxed_3475_ = lean_unbox(v_elimTrivial_3469_);
v_sz_boxed_3476_ = lean_unbox_usize(v_sz_3471_);
lean_dec(v_sz_3471_);
v_i_boxed_3477_ = lean_unbox_usize(v_i_3472_);
lean_dec(v_i_3472_);
v_res_3478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3475_, v_as_3470_, v_sz_boxed_3476_, v_i_boxed_3477_, v_b_3473_);
lean_dec_ref(v_as_3470_);
return v_res_3478_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3479_, lean_object* v_as_3480_, size_t v_sz_3481_, size_t v_i_3482_, lean_object* v_b_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
uint8_t v___x_3489_; 
v___x_3489_ = lean_usize_dec_lt(v_i_3482_, v_sz_3481_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v_b_3483_);
return v___x_3490_;
}
else
{
lean_object* v_snd_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3538_; 
v_snd_3491_ = lean_ctor_get(v_b_3483_, 1);
v_isSharedCheck_3538_ = !lean_is_exclusive(v_b_3483_);
if (v_isSharedCheck_3538_ == 0)
{
lean_object* v_unused_3539_; 
v_unused_3539_ = lean_ctor_get(v_b_3483_, 0);
lean_dec(v_unused_3539_);
v___x_3493_ = v_b_3483_;
v_isShared_3494_ = v_isSharedCheck_3538_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_snd_3491_);
lean_dec(v_b_3483_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3538_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v_a_3497_; lean_object* v_a_3504_; 
v___x_3495_ = lean_box(0);
v_a_3504_ = lean_array_uget_borrowed(v_as_3480_, v_i_3482_);
if (lean_obj_tag(v_a_3504_) == 0)
{
v_a_3497_ = v_snd_3491_;
goto v___jp_3496_;
}
else
{
lean_object* v_val_3505_; lean_object* v_fst_3506_; lean_object* v_snd_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3537_; 
v_val_3505_ = lean_ctor_get(v_a_3504_, 0);
v_fst_3506_ = lean_ctor_get(v_snd_3491_, 0);
v_snd_3507_ = lean_ctor_get(v_snd_3491_, 1);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_snd_3491_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3509_ = v_snd_3491_;
v_isShared_3510_ = v_isSharedCheck_3537_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_snd_3507_);
lean_inc(v_fst_3506_);
lean_dec(v_snd_3491_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3537_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
uint8_t v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = 0;
v___x_3512_ = l_Lean_LocalDecl_value_x3f(v_val_3505_, v___x_3511_);
if (lean_obj_tag(v___x_3512_) == 1)
{
lean_object* v_val_3513_; lean_object* v___x_3514_; 
v_val_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_val_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v___x_3514_ = l_Lean_LocalDecl_type(v_val_3505_);
if (lean_obj_tag(v___x_3514_) == 10)
{
lean_object* v_data_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; uint8_t v___x_3519_; uint8_t v___x_3520_; 
v_data_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_data_3515_);
lean_dec_ref_known(v___x_3514_, 2);
v___x_3516_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3517_ = lean_unsigned_to_nat(2u);
v___x_3518_ = l_Lean_KVMap_getNat(v_data_3515_, v___x_3516_, v___x_3517_);
lean_dec(v_data_3515_);
v___x_3519_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3518_);
lean_dec(v___x_3518_);
v___x_3520_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3519_, v_val_3513_, v_elimTrivial_3479_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3521_ = l_Lean_LocalDecl_fvarId(v_val_3505_);
v___x_3522_ = l_Lean_mkFVar(v___x_3521_);
v___x_3523_ = lean_array_push(v_fst_3506_, v___x_3522_);
v___x_3524_ = lean_array_push(v_snd_3507_, v_val_3513_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 1, v___x_3524_);
lean_ctor_set(v___x_3509_, 0, v___x_3523_);
v___x_3526_ = v___x_3509_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3523_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
v_a_3497_ = v___x_3526_;
goto v___jp_3496_;
}
}
else
{
lean_object* v___x_3529_; 
lean_dec(v_val_3513_);
if (v_isShared_3510_ == 0)
{
v___x_3529_ = v___x_3509_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_fst_3506_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_snd_3507_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
v_a_3497_ = v___x_3529_;
goto v___jp_3496_;
}
}
}
else
{
lean_object* v___x_3532_; 
lean_dec_ref(v___x_3514_);
lean_dec(v_val_3513_);
if (v_isShared_3510_ == 0)
{
v___x_3532_ = v___x_3509_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_fst_3506_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_snd_3507_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
v_a_3497_ = v___x_3532_;
goto v___jp_3496_;
}
}
}
else
{
lean_object* v___x_3535_; 
lean_dec(v___x_3512_);
if (v_isShared_3510_ == 0)
{
v___x_3535_ = v___x_3509_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_fst_3506_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_snd_3507_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
v_a_3497_ = v___x_3535_;
goto v___jp_3496_;
}
}
}
}
v___jp_3496_:
{
lean_object* v___x_3499_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 1, v_a_3497_);
lean_ctor_set(v___x_3493_, 0, v___x_3495_);
v___x_3499_ = v___x_3493_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_a_3497_);
v___x_3499_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
size_t v___x_3500_; size_t v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = ((size_t)1ULL);
v___x_3501_ = lean_usize_add(v_i_3482_, v___x_3500_);
v___x_3502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3479_, v_as_3480_, v_sz_3481_, v___x_3501_, v___x_3499_);
return v___x_3502_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_elimTrivial_3479_ = stack[0].m_num;
lean_object* v_as_3480_ = stack[1].m_obj;
size_t v_sz_3481_ = stack[2].m_num;
size_t v_i_3482_ = stack[3].m_num;
lean_object* v_b_3483_ = stack[4].m_obj;
lean_object* v___y_3484_ = stack[5].m_obj;
lean_object* v___y_3485_ = stack[6].m_obj;
lean_object* v___y_3486_ = stack[7].m_obj;
lean_object* v___y_3487_ = stack[8].m_obj;
lean_object* v_res_3540_;
v_res_3540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3479_, v_as_3480_, v_sz_3481_, v_i_3482_, v_b_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
stack->m_obj
 = v_res_3540_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3541_, lean_object* v_as_3542_, lean_object* v_sz_3543_, lean_object* v_i_3544_, lean_object* v_b_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
uint8_t v_elimTrivial_boxed_3551_; size_t v_sz_boxed_3552_; size_t v_i_boxed_3553_; lean_object* v_res_3554_; 
v_elimTrivial_boxed_3551_ = lean_unbox(v_elimTrivial_3541_);
v_sz_boxed_3552_ = lean_unbox_usize(v_sz_3543_);
lean_dec(v_sz_3543_);
v_i_boxed_3553_ = lean_unbox_usize(v_i_3544_);
lean_dec(v_i_3544_);
v_res_3554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3551_, v_as_3542_, v_sz_boxed_3552_, v_i_boxed_3553_, v_b_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec_ref(v_as_3542_);
return v_res_3554_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3555_, lean_object* v_as_3556_, size_t v_sz_3557_, size_t v_i_3558_, lean_object* v_b_3559_){
_start:
{
uint8_t v___x_3561_; 
v___x_3561_ = lean_usize_dec_lt(v_i_3558_, v_sz_3557_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; 
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_b_3559_);
return v___x_3562_;
}
else
{
lean_object* v_snd_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3610_; 
v_snd_3563_ = lean_ctor_get(v_b_3559_, 1);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_b_3559_);
if (v_isSharedCheck_3610_ == 0)
{
lean_object* v_unused_3611_; 
v_unused_3611_ = lean_ctor_get(v_b_3559_, 0);
lean_dec(v_unused_3611_);
v___x_3565_ = v_b_3559_;
v_isShared_3566_ = v_isSharedCheck_3610_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_snd_3563_);
lean_dec(v_b_3559_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3610_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; lean_object* v_a_3569_; lean_object* v_a_3576_; 
v___x_3567_ = lean_box(0);
v_a_3576_ = lean_array_uget_borrowed(v_as_3556_, v_i_3558_);
if (lean_obj_tag(v_a_3576_) == 0)
{
v_a_3569_ = v_snd_3563_;
goto v___jp_3568_;
}
else
{
lean_object* v_val_3577_; lean_object* v_fst_3578_; lean_object* v_snd_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3609_; 
v_val_3577_ = lean_ctor_get(v_a_3576_, 0);
v_fst_3578_ = lean_ctor_get(v_snd_3563_, 0);
v_snd_3579_ = lean_ctor_get(v_snd_3563_, 1);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_snd_3563_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3581_ = v_snd_3563_;
v_isShared_3582_ = v_isSharedCheck_3609_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_snd_3579_);
lean_inc(v_fst_3578_);
lean_dec(v_snd_3563_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3609_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
uint8_t v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = 0;
v___x_3584_ = l_Lean_LocalDecl_value_x3f(v_val_3577_, v___x_3583_);
if (lean_obj_tag(v___x_3584_) == 1)
{
lean_object* v_val_3585_; lean_object* v___x_3586_; 
v_val_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_val_3585_);
lean_dec_ref_known(v___x_3584_, 1);
v___x_3586_ = l_Lean_LocalDecl_type(v_val_3577_);
if (lean_obj_tag(v___x_3586_) == 10)
{
lean_object* v_data_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; uint8_t v___x_3592_; 
v_data_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_data_3587_);
lean_dec_ref_known(v___x_3586_, 2);
v___x_3588_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3589_ = lean_unsigned_to_nat(2u);
v___x_3590_ = l_Lean_KVMap_getNat(v_data_3587_, v___x_3588_, v___x_3589_);
lean_dec(v_data_3587_);
v___x_3591_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3590_);
lean_dec(v___x_3590_);
v___x_3592_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3591_, v_val_3585_, v_elimTrivial_3555_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3598_; 
v___x_3593_ = l_Lean_LocalDecl_fvarId(v_val_3577_);
v___x_3594_ = l_Lean_mkFVar(v___x_3593_);
v___x_3595_ = lean_array_push(v_fst_3578_, v___x_3594_);
v___x_3596_ = lean_array_push(v_snd_3579_, v_val_3585_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3596_);
lean_ctor_set(v___x_3581_, 0, v___x_3595_);
v___x_3598_ = v___x_3581_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
v_a_3569_ = v___x_3598_;
goto v___jp_3568_;
}
}
else
{
lean_object* v___x_3601_; 
lean_dec(v_val_3585_);
if (v_isShared_3582_ == 0)
{
v___x_3601_ = v___x_3581_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_fst_3578_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v_snd_3579_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
v_a_3569_ = v___x_3601_;
goto v___jp_3568_;
}
}
}
else
{
lean_object* v___x_3604_; 
lean_dec_ref(v___x_3586_);
lean_dec(v_val_3585_);
if (v_isShared_3582_ == 0)
{
v___x_3604_ = v___x_3581_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_fst_3578_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_snd_3579_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
v_a_3569_ = v___x_3604_;
goto v___jp_3568_;
}
}
}
else
{
lean_object* v___x_3607_; 
lean_dec(v___x_3584_);
if (v_isShared_3582_ == 0)
{
v___x_3607_ = v___x_3581_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_fst_3578_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_snd_3579_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
v_a_3569_ = v___x_3607_;
goto v___jp_3568_;
}
}
}
}
v___jp_3568_:
{
lean_object* v___x_3571_; 
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 1, v_a_3569_);
lean_ctor_set(v___x_3565_, 0, v___x_3567_);
v___x_3571_ = v___x_3565_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_a_3569_);
v___x_3571_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
size_t v___x_3572_; size_t v___x_3573_; 
v___x_3572_ = ((size_t)1ULL);
v___x_3573_ = lean_usize_add(v_i_3558_, v___x_3572_);
v_i_3558_ = v___x_3573_;
v_b_3559_ = v___x_3571_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_elimTrivial_3555_ = stack[0].m_num;
lean_object* v_as_3556_ = stack[1].m_obj;
size_t v_sz_3557_ = stack[2].m_num;
size_t v_i_3558_ = stack[3].m_num;
lean_object* v_b_3559_ = stack[4].m_obj;
lean_object* v_res_3612_;
v_res_3612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3555_, v_as_3556_, v_sz_3557_, v_i_3558_, v_b_3559_);
stack->m_obj
 = v_res_3612_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3613_, lean_object* v_as_3614_, lean_object* v_sz_3615_, lean_object* v_i_3616_, lean_object* v_b_3617_, lean_object* v___y_3618_){
_start:
{
uint8_t v_elimTrivial_boxed_3619_; size_t v_sz_boxed_3620_; size_t v_i_boxed_3621_; lean_object* v_res_3622_; 
v_elimTrivial_boxed_3619_ = lean_unbox(v_elimTrivial_3613_);
v_sz_boxed_3620_ = lean_unbox_usize(v_sz_3615_);
lean_dec(v_sz_3615_);
v_i_boxed_3621_ = lean_unbox_usize(v_i_3616_);
lean_dec(v_i_3616_);
v_res_3622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3619_, v_as_3614_, v_sz_boxed_3620_, v_i_boxed_3621_, v_b_3617_);
lean_dec_ref(v_as_3614_);
return v_res_3622_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3623_, lean_object* v_as_3624_, size_t v_sz_3625_, size_t v_i_3626_, lean_object* v_b_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
uint8_t v___x_3633_; 
v___x_3633_ = lean_usize_dec_lt(v_i_3626_, v_sz_3625_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; 
v___x_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3634_, 0, v_b_3627_);
return v___x_3634_;
}
else
{
lean_object* v_snd_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3682_; 
v_snd_3635_ = lean_ctor_get(v_b_3627_, 1);
v_isSharedCheck_3682_ = !lean_is_exclusive(v_b_3627_);
if (v_isSharedCheck_3682_ == 0)
{
lean_object* v_unused_3683_; 
v_unused_3683_ = lean_ctor_get(v_b_3627_, 0);
lean_dec(v_unused_3683_);
v___x_3637_ = v_b_3627_;
v_isShared_3638_ = v_isSharedCheck_3682_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_snd_3635_);
lean_dec(v_b_3627_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3682_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3639_; lean_object* v_a_3641_; lean_object* v_a_3648_; 
v___x_3639_ = lean_box(0);
v_a_3648_ = lean_array_uget_borrowed(v_as_3624_, v_i_3626_);
if (lean_obj_tag(v_a_3648_) == 0)
{
v_a_3641_ = v_snd_3635_;
goto v___jp_3640_;
}
else
{
lean_object* v_val_3649_; lean_object* v_fst_3650_; lean_object* v_snd_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3681_; 
v_val_3649_ = lean_ctor_get(v_a_3648_, 0);
v_fst_3650_ = lean_ctor_get(v_snd_3635_, 0);
v_snd_3651_ = lean_ctor_get(v_snd_3635_, 1);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_snd_3635_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3653_ = v_snd_3635_;
v_isShared_3654_ = v_isSharedCheck_3681_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_snd_3651_);
lean_inc(v_fst_3650_);
lean_dec(v_snd_3635_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3681_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
uint8_t v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = 0;
v___x_3656_ = l_Lean_LocalDecl_value_x3f(v_val_3649_, v___x_3655_);
if (lean_obj_tag(v___x_3656_) == 1)
{
lean_object* v_val_3657_; lean_object* v___x_3658_; 
v_val_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_val_3657_);
lean_dec_ref_known(v___x_3656_, 1);
v___x_3658_ = l_Lean_LocalDecl_type(v_val_3649_);
if (lean_obj_tag(v___x_3658_) == 10)
{
lean_object* v_data_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; uint8_t v___x_3664_; 
v_data_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_data_3659_);
lean_dec_ref_known(v___x_3658_, 2);
v___x_3660_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3661_ = lean_unsigned_to_nat(2u);
v___x_3662_ = l_Lean_KVMap_getNat(v_data_3659_, v___x_3660_, v___x_3661_);
lean_dec(v_data_3659_);
v___x_3663_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3662_);
lean_dec(v___x_3662_);
v___x_3664_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3663_, v_val_3657_, v_elimTrivial_3623_);
if (v___x_3664_ == 0)
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
v___x_3665_ = l_Lean_LocalDecl_fvarId(v_val_3649_);
v___x_3666_ = l_Lean_mkFVar(v___x_3665_);
v___x_3667_ = lean_array_push(v_fst_3650_, v___x_3666_);
v___x_3668_ = lean_array_push(v_snd_3651_, v_val_3657_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 1, v___x_3668_);
lean_ctor_set(v___x_3653_, 0, v___x_3667_);
v___x_3670_ = v___x_3653_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
v_a_3641_ = v___x_3670_;
goto v___jp_3640_;
}
}
else
{
lean_object* v___x_3673_; 
lean_dec(v_val_3657_);
if (v_isShared_3654_ == 0)
{
v___x_3673_ = v___x_3653_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_fst_3650_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_snd_3651_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
v_a_3641_ = v___x_3673_;
goto v___jp_3640_;
}
}
}
else
{
lean_object* v___x_3676_; 
lean_dec_ref(v___x_3658_);
lean_dec(v_val_3657_);
if (v_isShared_3654_ == 0)
{
v___x_3676_ = v___x_3653_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_fst_3650_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_snd_3651_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
v_a_3641_ = v___x_3676_;
goto v___jp_3640_;
}
}
}
else
{
lean_object* v___x_3679_; 
lean_dec(v___x_3656_);
if (v_isShared_3654_ == 0)
{
v___x_3679_ = v___x_3653_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_fst_3650_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_snd_3651_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
v_a_3641_ = v___x_3679_;
goto v___jp_3640_;
}
}
}
}
v___jp_3640_:
{
lean_object* v___x_3643_; 
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 1, v_a_3641_);
lean_ctor_set(v___x_3637_, 0, v___x_3639_);
v___x_3643_ = v___x_3637_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_a_3641_);
v___x_3643_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
size_t v___x_3644_; size_t v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = ((size_t)1ULL);
v___x_3645_ = lean_usize_add(v_i_3626_, v___x_3644_);
v___x_3646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3623_, v_as_3624_, v_sz_3625_, v___x_3645_, v___x_3643_);
return v___x_3646_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_elimTrivial_3623_ = stack[0].m_num;
lean_object* v_as_3624_ = stack[1].m_obj;
size_t v_sz_3625_ = stack[2].m_num;
size_t v_i_3626_ = stack[3].m_num;
lean_object* v_b_3627_ = stack[4].m_obj;
lean_object* v___y_3628_ = stack[5].m_obj;
lean_object* v___y_3629_ = stack[6].m_obj;
lean_object* v___y_3630_ = stack[7].m_obj;
lean_object* v___y_3631_ = stack[8].m_obj;
lean_object* v_res_3684_;
v_res_3684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3623_, v_as_3624_, v_sz_3625_, v_i_3626_, v_b_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
stack->m_obj
 = v_res_3684_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3685_, lean_object* v_as_3686_, lean_object* v_sz_3687_, lean_object* v_i_3688_, lean_object* v_b_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
uint8_t v_elimTrivial_boxed_3695_; size_t v_sz_boxed_3696_; size_t v_i_boxed_3697_; lean_object* v_res_3698_; 
v_elimTrivial_boxed_3695_ = lean_unbox(v_elimTrivial_3685_);
v_sz_boxed_3696_ = lean_unbox_usize(v_sz_3687_);
lean_dec(v_sz_3687_);
v_i_boxed_3697_ = lean_unbox_usize(v_i_3688_);
lean_dec(v_i_3688_);
v_res_3698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3695_, v_as_3686_, v_sz_boxed_3696_, v_i_boxed_3697_, v_b_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_as_3686_);
return v_res_3698_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3699_, uint8_t v_elimTrivial_3700_, lean_object* v_n_3701_, lean_object* v_b_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
if (lean_obj_tag(v_n_3701_) == 0)
{
lean_object* v_cs_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; size_t v_sz_3711_; size_t v___x_3712_; lean_object* v___x_3713_; 
v_cs_3708_ = lean_ctor_get(v_n_3701_, 0);
v___x_3709_ = lean_box(0);
v___x_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v_b_3702_);
v_sz_3711_ = lean_array_size(v_cs_3708_);
v___x_3712_ = ((size_t)0ULL);
v___x_3713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3699_, v_elimTrivial_3700_, v_cs_3708_, v_sz_3711_, v___x_3712_, v___x_3710_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3728_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3716_ = v___x_3713_;
v_isShared_3717_ = v_isSharedCheck_3728_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3713_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3728_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v_fst_3718_; 
v_fst_3718_ = lean_ctor_get(v_a_3714_, 0);
if (lean_obj_tag(v_fst_3718_) == 0)
{
lean_object* v_snd_3719_; lean_object* v___x_3720_; lean_object* v___x_3722_; 
v_snd_3719_ = lean_ctor_get(v_a_3714_, 1);
lean_inc(v_snd_3719_);
lean_dec(v_a_3714_);
v___x_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3720_, 0, v_snd_3719_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3720_);
v___x_3722_ = v___x_3716_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
else
{
lean_object* v_val_3724_; lean_object* v___x_3726_; 
lean_inc_ref(v_fst_3718_);
lean_dec(v_a_3714_);
v_val_3724_ = lean_ctor_get(v_fst_3718_, 0);
lean_inc(v_val_3724_);
lean_dec_ref_known(v_fst_3718_, 1);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v_val_3724_);
v___x_3726_ = v___x_3716_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_val_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
v_a_3729_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3713_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3713_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
else
{
lean_object* v_vs_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; size_t v_sz_3740_; size_t v___x_3741_; lean_object* v___x_3742_; 
v_vs_3737_ = lean_ctor_get(v_n_3701_, 0);
v___x_3738_ = lean_box(0);
v___x_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set(v___x_3739_, 1, v_b_3702_);
v_sz_3740_ = lean_array_size(v_vs_3737_);
v___x_3741_ = ((size_t)0ULL);
v___x_3742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3700_, v_vs_3737_, v_sz_3740_, v___x_3741_, v___x_3739_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3757_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3745_ = v___x_3742_;
v_isShared_3746_ = v_isSharedCheck_3757_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3742_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3757_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v_fst_3747_; 
v_fst_3747_ = lean_ctor_get(v_a_3743_, 0);
if (lean_obj_tag(v_fst_3747_) == 0)
{
lean_object* v_snd_3748_; lean_object* v___x_3749_; lean_object* v___x_3751_; 
v_snd_3748_ = lean_ctor_get(v_a_3743_, 1);
lean_inc(v_snd_3748_);
lean_dec(v_a_3743_);
v___x_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3749_, 0, v_snd_3748_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v___x_3749_);
v___x_3751_ = v___x_3745_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
else
{
lean_object* v_val_3753_; lean_object* v___x_3755_; 
lean_inc_ref(v_fst_3747_);
lean_dec(v_a_3743_);
v_val_3753_ = lean_ctor_get(v_fst_3747_, 0);
lean_inc(v_val_3753_);
lean_dec_ref_known(v_fst_3747_, 1);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v_val_3753_);
v___x_3755_ = v___x_3745_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_val_3753_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
else
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
v_a_3758_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3742_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3742_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3699_ = stack[0].m_obj;
uint8_t v_elimTrivial_3700_ = stack[1].m_num;
lean_object* v_n_3701_ = stack[2].m_obj;
lean_object* v_b_3702_ = stack[3].m_obj;
lean_object* v___y_3703_ = stack[4].m_obj;
lean_object* v___y_3704_ = stack[5].m_obj;
lean_object* v___y_3705_ = stack[6].m_obj;
lean_object* v___y_3706_ = stack[7].m_obj;
lean_object* v_res_3766_;
v_res_3766_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3699_, v_elimTrivial_3700_, v_n_3701_, v_b_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
stack->m_obj
 = v_res_3766_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3767_, uint8_t v_elimTrivial_3768_, lean_object* v_as_3769_, size_t v_sz_3770_, size_t v_i_3771_, lean_object* v_b_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
uint8_t v___x_3778_; 
v___x_3778_ = lean_usize_dec_lt(v_i_3771_, v_sz_3770_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; 
v___x_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3779_, 0, v_b_3772_);
return v___x_3779_;
}
else
{
lean_object* v_snd_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3814_; 
v_snd_3780_ = lean_ctor_get(v_b_3772_, 1);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_b_3772_);
if (v_isSharedCheck_3814_ == 0)
{
lean_object* v_unused_3815_; 
v_unused_3815_ = lean_ctor_get(v_b_3772_, 0);
lean_dec(v_unused_3815_);
v___x_3782_ = v_b_3772_;
v_isShared_3783_ = v_isSharedCheck_3814_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_snd_3780_);
lean_dec(v_b_3772_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3814_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3784_; lean_object* v_a_3785_; lean_object* v___x_3786_; 
v___x_3784_ = lean_box(0);
v_a_3785_ = lean_array_uget_borrowed(v_as_3769_, v_i_3771_);
lean_inc(v_snd_3780_);
v___x_3786_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3767_, v_elimTrivial_3768_, v_a_3785_, v_snd_3780_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3805_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3805_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3805_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
if (lean_obj_tag(v_a_3787_) == 0)
{
lean_object* v___x_3791_; lean_object* v___x_3793_; 
v___x_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3791_, 0, v_a_3787_);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v___x_3791_);
v___x_3793_ = v___x_3782_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_snd_3780_);
v___x_3793_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
lean_object* v___x_3795_; 
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3793_);
v___x_3795_ = v___x_3789_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; 
lean_del_object(v___x_3789_);
lean_dec(v_snd_3780_);
v_a_3798_ = lean_ctor_get(v_a_3787_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v_a_3787_, 1);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v_a_3798_);
lean_ctor_set(v___x_3782_, 0, v___x_3784_);
v___x_3800_ = v___x_3782_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_a_3798_);
v___x_3800_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
size_t v___x_3801_; size_t v___x_3802_; 
v___x_3801_ = ((size_t)1ULL);
v___x_3802_ = lean_usize_add(v_i_3771_, v___x_3801_);
v_i_3771_ = v___x_3802_;
v_b_3772_ = v___x_3800_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_del_object(v___x_3782_);
lean_dec(v_snd_3780_);
v_a_3806_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3786_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3786_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3767_ = stack[0].m_obj;
uint8_t v_elimTrivial_3768_ = stack[1].m_num;
lean_object* v_as_3769_ = stack[2].m_obj;
size_t v_sz_3770_ = stack[3].m_num;
size_t v_i_3771_ = stack[4].m_num;
lean_object* v_b_3772_ = stack[5].m_obj;
lean_object* v___y_3773_ = stack[6].m_obj;
lean_object* v___y_3774_ = stack[7].m_obj;
lean_object* v___y_3775_ = stack[8].m_obj;
lean_object* v___y_3776_ = stack[9].m_obj;
lean_object* v_res_3816_;
v_res_3816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3767_, v_elimTrivial_3768_, v_as_3769_, v_sz_3770_, v_i_3771_, v_b_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
stack->m_obj
 = v_res_3816_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3817_, lean_object* v_elimTrivial_3818_, lean_object* v_as_3819_, lean_object* v_sz_3820_, lean_object* v_i_3821_, lean_object* v_b_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
uint8_t v_elimTrivial_boxed_3828_; size_t v_sz_boxed_3829_; size_t v_i_boxed_3830_; lean_object* v_res_3831_; 
v_elimTrivial_boxed_3828_ = lean_unbox(v_elimTrivial_3818_);
v_sz_boxed_3829_ = lean_unbox_usize(v_sz_3820_);
lean_dec(v_sz_3820_);
v_i_boxed_3830_ = lean_unbox_usize(v_i_3821_);
lean_dec(v_i_3821_);
v_res_3831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3817_, v_elimTrivial_boxed_3828_, v_as_3819_, v_sz_boxed_3829_, v_i_boxed_3830_, v_b_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec_ref(v_as_3819_);
lean_dec_ref(v_init_3817_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3832_, lean_object* v_elimTrivial_3833_, lean_object* v_n_3834_, lean_object* v_b_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
uint8_t v_elimTrivial_boxed_3841_; lean_object* v_res_3842_; 
v_elimTrivial_boxed_3841_ = lean_unbox(v_elimTrivial_3833_);
v_res_3842_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3832_, v_elimTrivial_boxed_3841_, v_n_3834_, v_b_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec_ref(v_n_3834_);
lean_dec_ref(v_init_3832_);
return v_res_3842_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3843_, lean_object* v_t_3844_, lean_object* v_init_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v_root_3851_; lean_object* v_tail_3852_; lean_object* v___x_3853_; 
v_root_3851_ = lean_ctor_get(v_t_3844_, 0);
v_tail_3852_ = lean_ctor_get(v_t_3844_, 1);
lean_inc_ref(v_init_3845_);
v___x_3853_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3845_, v_elimTrivial_3843_, v_root_3851_, v_init_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec_ref(v_init_3845_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3890_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3856_ = v___x_3853_;
v_isShared_3857_ = v_isSharedCheck_3890_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3853_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3890_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
if (lean_obj_tag(v_a_3854_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; 
v_a_3858_ = lean_ctor_get(v_a_3854_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v_a_3854_, 1);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v_a_3858_);
v___x_3860_ = v___x_3856_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3858_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; size_t v_sz_3865_; size_t v___x_3866_; lean_object* v___x_3867_; 
lean_del_object(v___x_3856_);
v_a_3862_ = lean_ctor_get(v_a_3854_, 0);
lean_inc(v_a_3862_);
lean_dec_ref_known(v_a_3854_, 1);
v___x_3863_ = lean_box(0);
v___x_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
lean_ctor_set(v___x_3864_, 1, v_a_3862_);
v_sz_3865_ = lean_array_size(v_tail_3852_);
v___x_3866_ = ((size_t)0ULL);
v___x_3867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3843_, v_tail_3852_, v_sz_3865_, v___x_3866_, v___x_3864_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3881_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3870_ = v___x_3867_;
v_isShared_3871_ = v_isSharedCheck_3881_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3867_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3881_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v_fst_3872_; 
v_fst_3872_ = lean_ctor_get(v_a_3868_, 0);
if (lean_obj_tag(v_fst_3872_) == 0)
{
lean_object* v_snd_3873_; lean_object* v___x_3875_; 
v_snd_3873_ = lean_ctor_get(v_a_3868_, 1);
lean_inc(v_snd_3873_);
lean_dec(v_a_3868_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v_snd_3873_);
v___x_3875_ = v___x_3870_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_snd_3873_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
else
{
lean_object* v_val_3877_; lean_object* v___x_3879_; 
lean_inc_ref(v_fst_3872_);
lean_dec(v_a_3868_);
v_val_3877_ = lean_ctor_get(v_fst_3872_, 0);
lean_inc(v_val_3877_);
lean_dec_ref_known(v_fst_3872_, 1);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v_val_3877_);
v___x_3879_ = v___x_3870_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_val_3877_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
v_a_3882_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3867_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3867_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
v_a_3891_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3853_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3853_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_elimTrivial_3843_ = stack[0].m_num;
lean_object* v_t_3844_ = stack[1].m_obj;
lean_object* v_init_3845_ = stack[2].m_obj;
lean_object* v___y_3846_ = stack[3].m_obj;
lean_object* v___y_3847_ = stack[4].m_obj;
lean_object* v___y_3848_ = stack[5].m_obj;
lean_object* v___y_3849_ = stack[6].m_obj;
lean_object* v_res_3899_;
v_res_3899_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_3843_, v_t_3844_, v_init_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
stack->m_obj
 = v_res_3899_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_3900_, lean_object* v_t_3901_, lean_object* v_init_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
uint8_t v_elimTrivial_boxed_3908_; lean_object* v_res_3909_; 
v_elimTrivial_boxed_3908_ = lean_unbox(v_elimTrivial_3900_);
v_res_3909_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_3908_, v_t_3901_, v_init_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec_ref(v_t_3901_);
return v_res_3909_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_3910_, size_t v_sz_3911_, size_t v_i_3912_, lean_object* v_b_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
uint8_t v___x_3919_; 
v___x_3919_ = lean_usize_dec_lt(v_i_3912_, v_sz_3911_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; 
v___x_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3920_, 0, v_b_3913_);
return v___x_3920_;
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v_a_3921_ = lean_array_uget_borrowed(v_as_3910_, v_i_3912_);
v___x_3922_ = l_Lean_Expr_fvarId_x21(v_a_3921_);
v___x_3923_ = l_Lean_MVarId_tryClear(v_b_3913_, v___x_3922_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; size_t v___x_3925_; size_t v___x_3926_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v___x_3925_ = ((size_t)1ULL);
v___x_3926_ = lean_usize_add(v_i_3912_, v___x_3925_);
v_i_3912_ = v___x_3926_;
v_b_3913_ = v_a_3924_;
goto _start;
}
else
{
return v___x_3923_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3910_ = stack[0].m_obj;
size_t v_sz_3911_ = stack[1].m_num;
size_t v_i_3912_ = stack[2].m_num;
lean_object* v_b_3913_ = stack[3].m_obj;
lean_object* v___y_3914_ = stack[4].m_obj;
lean_object* v___y_3915_ = stack[5].m_obj;
lean_object* v___y_3916_ = stack[6].m_obj;
lean_object* v___y_3917_ = stack[7].m_obj;
lean_object* v_res_3928_;
v_res_3928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3910_, v_sz_3911_, v_i_3912_, v_b_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
stack->m_obj
 = v_res_3928_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_3929_, lean_object* v_sz_3930_, lean_object* v_i_3931_, lean_object* v_b_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
size_t v_sz_boxed_3938_; size_t v_i_boxed_3939_; lean_object* v_res_3940_; 
v_sz_boxed_3938_ = lean_unbox_usize(v_sz_3930_);
lean_dec(v_sz_3930_);
v_i_boxed_3939_ = lean_unbox_usize(v_i_3931_);
lean_dec(v_i_3931_);
v_res_3940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3929_, v_sz_boxed_3938_, v_i_boxed_3939_, v_b_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec_ref(v_as_3929_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_3941_, lean_object* v_x_3942_, lean_object* v_x_3943_, lean_object* v_x_3944_){
_start:
{
lean_object* v_ks_3945_; lean_object* v_vs_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3970_; 
v_ks_3945_ = lean_ctor_get(v_x_3941_, 0);
v_vs_3946_ = lean_ctor_get(v_x_3941_, 1);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_x_3941_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3948_ = v_x_3941_;
v_isShared_3949_ = v_isSharedCheck_3970_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_vs_3946_);
lean_inc(v_ks_3945_);
lean_dec(v_x_3941_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3970_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3950_; uint8_t v___x_3951_; 
v___x_3950_ = lean_array_get_size(v_ks_3945_);
v___x_3951_ = lean_nat_dec_lt(v_x_3942_, v___x_3950_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3955_; 
lean_dec(v_x_3942_);
v___x_3952_ = lean_array_push(v_ks_3945_, v_x_3943_);
v___x_3953_ = lean_array_push(v_vs_3946_, v_x_3944_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v___x_3953_);
lean_ctor_set(v___x_3948_, 0, v___x_3952_);
v___x_3955_ = v___x_3948_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3952_);
lean_ctor_set(v_reuseFailAlloc_3956_, 1, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
else
{
lean_object* v_k_x27_3957_; uint8_t v___x_3958_; 
v_k_x27_3957_ = lean_array_fget_borrowed(v_ks_3945_, v_x_3942_);
v___x_3958_ = l_Lean_instBEqMVarId_beq(v_x_3943_, v_k_x27_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3960_; 
if (v_isShared_3949_ == 0)
{
v___x_3960_ = v___x_3948_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_ks_3945_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_vs_3946_);
v___x_3960_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_unsigned_to_nat(1u);
v___x_3962_ = lean_nat_add(v_x_3942_, v___x_3961_);
lean_dec(v_x_3942_);
v_x_3941_ = v___x_3960_;
v_x_3942_ = v___x_3962_;
goto _start;
}
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3968_; 
v___x_3965_ = lean_array_fset(v_ks_3945_, v_x_3942_, v_x_3943_);
v___x_3966_ = lean_array_fset(v_vs_3946_, v_x_3942_, v_x_3944_);
lean_dec(v_x_3942_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v___x_3966_);
lean_ctor_set(v___x_3948_, 0, v___x_3965_);
v___x_3968_ = v___x_3948_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3965_);
lean_ctor_set(v_reuseFailAlloc_3969_, 1, v___x_3966_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_3971_, lean_object* v_k_3972_, lean_object* v_v_3973_){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = lean_unsigned_to_nat(0u);
v___x_3975_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_3971_, v___x_3974_, v_k_3972_, v_v_3973_);
return v___x_3975_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3976_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_3977_, size_t v_x_3978_, size_t v_x_3979_, lean_object* v_x_3980_, lean_object* v_x_3981_){
_start:
{
if (lean_obj_tag(v_x_3977_) == 0)
{
lean_object* v_es_3982_; size_t v___x_3983_; size_t v___x_3984_; lean_object* v_j_3985_; lean_object* v___x_3986_; uint8_t v___x_3987_; 
v_es_3982_ = lean_ctor_get(v_x_3977_, 0);
v___x_3983_ = ((size_t)31ULL);
v___x_3984_ = lean_usize_land(v_x_3978_, v___x_3983_);
v_j_3985_ = lean_usize_to_nat(v___x_3984_);
v___x_3986_ = lean_array_get_size(v_es_3982_);
v___x_3987_ = lean_nat_dec_lt(v_j_3985_, v___x_3986_);
if (v___x_3987_ == 0)
{
lean_dec(v_j_3985_);
lean_dec(v_x_3981_);
lean_dec(v_x_3980_);
return v_x_3977_;
}
else
{
lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_4026_; 
lean_inc_ref(v_es_3982_);
v_isSharedCheck_4026_ = !lean_is_exclusive(v_x_3977_);
if (v_isSharedCheck_4026_ == 0)
{
lean_object* v_unused_4027_; 
v_unused_4027_ = lean_ctor_get(v_x_3977_, 0);
lean_dec(v_unused_4027_);
v___x_3989_ = v_x_3977_;
v_isShared_3990_ = v_isSharedCheck_4026_;
goto v_resetjp_3988_;
}
else
{
lean_dec(v_x_3977_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_4026_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v_v_3991_; lean_object* v___x_3992_; lean_object* v_xs_x27_3993_; lean_object* v___y_3995_; 
v_v_3991_ = lean_array_fget(v_es_3982_, v_j_3985_);
v___x_3992_ = lean_box(0);
v_xs_x27_3993_ = lean_array_fset(v_es_3982_, v_j_3985_, v___x_3992_);
switch(lean_obj_tag(v_v_3991_))
{
case 0:
{
lean_object* v_key_4000_; lean_object* v_val_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4011_; 
v_key_4000_ = lean_ctor_get(v_v_3991_, 0);
v_val_4001_ = lean_ctor_get(v_v_3991_, 1);
v_isSharedCheck_4011_ = !lean_is_exclusive(v_v_3991_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4003_ = v_v_3991_;
v_isShared_4004_ = v_isSharedCheck_4011_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_val_4001_);
lean_inc(v_key_4000_);
lean_dec(v_v_3991_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4011_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
uint8_t v___x_4005_; 
v___x_4005_ = l_Lean_instBEqMVarId_beq(v_x_3980_, v_key_4000_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_del_object(v___x_4003_);
v___x_4006_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4000_, v_val_4001_, v_x_3980_, v_x_3981_);
v___x_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
v___y_3995_ = v___x_4007_;
goto v___jp_3994_;
}
else
{
lean_object* v___x_4009_; 
lean_dec(v_val_4001_);
lean_dec(v_key_4000_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 1, v_x_3981_);
lean_ctor_set(v___x_4003_, 0, v_x_3980_);
v___x_4009_ = v___x_4003_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_x_3980_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v_x_3981_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
v___y_3995_ = v___x_4009_;
goto v___jp_3994_;
}
}
}
}
case 1:
{
lean_object* v_node_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4024_; 
v_node_4012_ = lean_ctor_get(v_v_3991_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v_v_3991_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4014_ = v_v_3991_;
v_isShared_4015_ = v_isSharedCheck_4024_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_node_4012_);
lean_dec(v_v_3991_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4024_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
size_t v___x_4016_; size_t v___x_4017_; size_t v___x_4018_; size_t v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4022_; 
v___x_4016_ = ((size_t)5ULL);
v___x_4017_ = lean_usize_shift_right(v_x_3978_, v___x_4016_);
v___x_4018_ = ((size_t)1ULL);
v___x_4019_ = lean_usize_add(v_x_3979_, v___x_4018_);
v___x_4020_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_4012_, v___x_4017_, v___x_4019_, v_x_3980_, v_x_3981_);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 0, v___x_4020_);
v___x_4022_ = v___x_4014_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___x_4020_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
v___y_3995_ = v___x_4022_;
goto v___jp_3994_;
}
}
}
default: 
{
lean_object* v___x_4025_; 
v___x_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4025_, 0, v_x_3980_);
lean_ctor_set(v___x_4025_, 1, v_x_3981_);
v___y_3995_ = v___x_4025_;
goto v___jp_3994_;
}
}
v___jp_3994_:
{
lean_object* v___x_3996_; lean_object* v___x_3998_; 
v___x_3996_ = lean_array_fset(v_xs_x27_3993_, v_j_3985_, v___y_3995_);
lean_dec(v_j_3985_);
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v___x_3996_);
v___x_3998_ = v___x_3989_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3996_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
}
else
{
lean_object* v_ks_4028_; lean_object* v_vs_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4047_; 
v_ks_4028_ = lean_ctor_get(v_x_3977_, 0);
v_vs_4029_ = lean_ctor_get(v_x_3977_, 1);
v_isSharedCheck_4047_ = !lean_is_exclusive(v_x_3977_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4031_ = v_x_3977_;
v_isShared_4032_ = v_isSharedCheck_4047_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_vs_4029_);
lean_inc(v_ks_4028_);
lean_dec(v_x_3977_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4047_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_ks_4028_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v_vs_4029_);
v___x_4034_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v_newNode_4035_; size_t v___x_4036_; uint8_t v___x_4037_; 
v_newNode_4035_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_4034_, v_x_3980_, v_x_3981_);
v___x_4036_ = ((size_t)7ULL);
v___x_4037_ = lean_usize_dec_le(v___x_4036_, v_x_3979_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; lean_object* v___x_4039_; uint8_t v___x_4040_; 
v___x_4038_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4035_);
v___x_4039_ = lean_unsigned_to_nat(4u);
v___x_4040_ = lean_nat_dec_lt(v___x_4038_, v___x_4039_);
lean_dec(v___x_4038_);
if (v___x_4040_ == 0)
{
lean_object* v_ks_4041_; lean_object* v_vs_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v_ks_4041_ = lean_ctor_get(v_newNode_4035_, 0);
lean_inc_ref(v_ks_4041_);
v_vs_4042_ = lean_ctor_get(v_newNode_4035_, 1);
lean_inc_ref(v_vs_4042_);
lean_dec_ref(v_newNode_4035_);
v___x_4043_ = lean_unsigned_to_nat(0u);
v___x_4044_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_4045_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3979_, v_ks_4041_, v_vs_4042_, v___x_4043_, v___x_4044_);
lean_dec_ref(v_vs_4042_);
lean_dec_ref(v_ks_4041_);
return v___x_4045_;
}
else
{
return v_newNode_4035_;
}
}
else
{
return v_newNode_4035_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3977_ = stack[0].m_obj;
size_t v_x_3978_ = stack[1].m_num;
size_t v_x_3979_ = stack[2].m_num;
lean_object* v_x_3980_ = stack[3].m_obj;
lean_object* v_x_3981_ = stack[4].m_obj;
lean_object* v_res_4048_;
v_res_4048_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_3977_, v_x_3978_, v_x_3979_, v_x_3980_, v_x_3981_);
stack->m_obj
 = v_res_4048_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_4049_, lean_object* v_keys_4050_, lean_object* v_vals_4051_, lean_object* v_i_4052_, lean_object* v_entries_4053_){
_start:
{
lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4054_ = lean_array_get_size(v_keys_4050_);
v___x_4055_ = lean_nat_dec_lt(v_i_4052_, v___x_4054_);
if (v___x_4055_ == 0)
{
lean_dec(v_i_4052_);
return v_entries_4053_;
}
else
{
lean_object* v_k_4056_; lean_object* v_v_4057_; uint64_t v___x_4058_; size_t v_h_4059_; size_t v___x_4060_; lean_object* v___x_4061_; size_t v___x_4062_; size_t v___x_4063_; size_t v___x_4064_; size_t v_h_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v_k_4056_ = lean_array_fget_borrowed(v_keys_4050_, v_i_4052_);
v_v_4057_ = lean_array_fget_borrowed(v_vals_4051_, v_i_4052_);
v___x_4058_ = l_Lean_instHashableMVarId_hash(v_k_4056_);
v_h_4059_ = lean_uint64_to_usize(v___x_4058_);
v___x_4060_ = ((size_t)5ULL);
v___x_4061_ = lean_unsigned_to_nat(1u);
v___x_4062_ = ((size_t)1ULL);
v___x_4063_ = lean_usize_sub(v_depth_4049_, v___x_4062_);
v___x_4064_ = lean_usize_mul(v___x_4060_, v___x_4063_);
v_h_4065_ = lean_usize_shift_right(v_h_4059_, v___x_4064_);
v___x_4066_ = lean_nat_add(v_i_4052_, v___x_4061_);
lean_dec(v_i_4052_);
lean_inc(v_v_4057_);
lean_inc(v_k_4056_);
v___x_4067_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_4053_, v_h_4065_, v_depth_4049_, v_k_4056_, v_v_4057_);
v_i_4052_ = v___x_4066_;
v_entries_4053_ = v___x_4067_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_4049_ = stack[0].m_num;
lean_object* v_keys_4050_ = stack[1].m_obj;
lean_object* v_vals_4051_ = stack[2].m_obj;
lean_object* v_i_4052_ = stack[3].m_obj;
lean_object* v_entries_4053_ = stack[4].m_obj;
lean_object* v_res_4069_;
v_res_4069_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4049_, v_keys_4050_, v_vals_4051_, v_i_4052_, v_entries_4053_);
stack->m_obj
 = v_res_4069_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_4070_, lean_object* v_keys_4071_, lean_object* v_vals_4072_, lean_object* v_i_4073_, lean_object* v_entries_4074_){
_start:
{
size_t v_depth_boxed_4075_; lean_object* v_res_4076_; 
v_depth_boxed_4075_ = lean_unbox_usize(v_depth_4070_);
lean_dec(v_depth_4070_);
v_res_4076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_4075_, v_keys_4071_, v_vals_4072_, v_i_4073_, v_entries_4074_);
lean_dec_ref(v_vals_4072_);
lean_dec_ref(v_keys_4071_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_4077_, lean_object* v_x_4078_, lean_object* v_x_4079_, lean_object* v_x_4080_, lean_object* v_x_4081_){
_start:
{
size_t v_x_8286__boxed_4082_; size_t v_x_8287__boxed_4083_; lean_object* v_res_4084_; 
v_x_8286__boxed_4082_ = lean_unbox_usize(v_x_4078_);
lean_dec(v_x_4078_);
v_x_8287__boxed_4083_ = lean_unbox_usize(v_x_4079_);
lean_dec(v_x_4079_);
v_res_4084_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4077_, v_x_8286__boxed_4082_, v_x_8287__boxed_4083_, v_x_4080_, v_x_4081_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_4085_, lean_object* v_x_4086_, lean_object* v_x_4087_){
_start:
{
uint64_t v___x_4088_; size_t v___x_4089_; size_t v___x_4090_; lean_object* v___x_4091_; 
v___x_4088_ = l_Lean_instHashableMVarId_hash(v_x_4086_);
v___x_4089_ = lean_uint64_to_usize(v___x_4088_);
v___x_4090_ = ((size_t)1ULL);
v___x_4091_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4085_, v___x_4089_, v___x_4090_, v_x_4086_, v_x_4087_);
return v___x_4091_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4092_, lean_object* v_val_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v___x_4096_; lean_object* v_mctx_4097_; lean_object* v_cache_4098_; lean_object* v_zetaDeltaFVarIds_4099_; lean_object* v_postponed_4100_; lean_object* v_diag_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4131_; 
v___x_4096_ = lean_st_ref_take(v___y_4094_);
v_mctx_4097_ = lean_ctor_get(v___x_4096_, 0);
v_cache_4098_ = lean_ctor_get(v___x_4096_, 1);
v_zetaDeltaFVarIds_4099_ = lean_ctor_get(v___x_4096_, 2);
v_postponed_4100_ = lean_ctor_get(v___x_4096_, 3);
v_diag_4101_ = lean_ctor_get(v___x_4096_, 4);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4103_ = v___x_4096_;
v_isShared_4104_ = v_isSharedCheck_4131_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_diag_4101_);
lean_inc(v_postponed_4100_);
lean_inc(v_zetaDeltaFVarIds_4099_);
lean_inc(v_cache_4098_);
lean_inc(v_mctx_4097_);
lean_dec(v___x_4096_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4131_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v_depth_4105_; lean_object* v_levelAssignDepth_4106_; lean_object* v_lmvarCounter_4107_; lean_object* v_mvarCounter_4108_; lean_object* v_lDecls_4109_; lean_object* v_decls_4110_; lean_object* v_userNames_4111_; lean_object* v_lAssignment_4112_; lean_object* v_eAssignment_4113_; lean_object* v_dAssignment_4114_; lean_object* v_instanceTypedMVars_4115_; lean_object* v_synthNormMemo_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4130_; 
v_depth_4105_ = lean_ctor_get(v_mctx_4097_, 0);
v_levelAssignDepth_4106_ = lean_ctor_get(v_mctx_4097_, 1);
v_lmvarCounter_4107_ = lean_ctor_get(v_mctx_4097_, 2);
v_mvarCounter_4108_ = lean_ctor_get(v_mctx_4097_, 3);
v_lDecls_4109_ = lean_ctor_get(v_mctx_4097_, 4);
v_decls_4110_ = lean_ctor_get(v_mctx_4097_, 5);
v_userNames_4111_ = lean_ctor_get(v_mctx_4097_, 6);
v_lAssignment_4112_ = lean_ctor_get(v_mctx_4097_, 7);
v_eAssignment_4113_ = lean_ctor_get(v_mctx_4097_, 8);
v_dAssignment_4114_ = lean_ctor_get(v_mctx_4097_, 9);
v_instanceTypedMVars_4115_ = lean_ctor_get(v_mctx_4097_, 10);
v_synthNormMemo_4116_ = lean_ctor_get(v_mctx_4097_, 11);
v_isSharedCheck_4130_ = !lean_is_exclusive(v_mctx_4097_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4118_ = v_mctx_4097_;
v_isShared_4119_ = v_isSharedCheck_4130_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_synthNormMemo_4116_);
lean_inc(v_instanceTypedMVars_4115_);
lean_inc(v_dAssignment_4114_);
lean_inc(v_eAssignment_4113_);
lean_inc(v_lAssignment_4112_);
lean_inc(v_userNames_4111_);
lean_inc(v_decls_4110_);
lean_inc(v_lDecls_4109_);
lean_inc(v_mvarCounter_4108_);
lean_inc(v_lmvarCounter_4107_);
lean_inc(v_levelAssignDepth_4106_);
lean_inc(v_depth_4105_);
lean_dec(v_mctx_4097_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4130_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4123_; 
v___x_4120_ = lean_box(0);
v___x_4121_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4113_, v_mvarId_4092_, v_val_4093_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 8, v___x_4121_);
v___x_4123_ = v___x_4118_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_depth_4105_);
lean_ctor_set(v_reuseFailAlloc_4129_, 1, v_levelAssignDepth_4106_);
lean_ctor_set(v_reuseFailAlloc_4129_, 2, v_lmvarCounter_4107_);
lean_ctor_set(v_reuseFailAlloc_4129_, 3, v_mvarCounter_4108_);
lean_ctor_set(v_reuseFailAlloc_4129_, 4, v_lDecls_4109_);
lean_ctor_set(v_reuseFailAlloc_4129_, 5, v_decls_4110_);
lean_ctor_set(v_reuseFailAlloc_4129_, 6, v_userNames_4111_);
lean_ctor_set(v_reuseFailAlloc_4129_, 7, v_lAssignment_4112_);
lean_ctor_set(v_reuseFailAlloc_4129_, 8, v___x_4121_);
lean_ctor_set(v_reuseFailAlloc_4129_, 9, v_dAssignment_4114_);
lean_ctor_set(v_reuseFailAlloc_4129_, 10, v_instanceTypedMVars_4115_);
lean_ctor_set(v_reuseFailAlloc_4129_, 11, v_synthNormMemo_4116_);
v___x_4123_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
lean_object* v___x_4125_; 
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 0, v___x_4123_);
v___x_4125_ = v___x_4103_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4123_);
lean_ctor_set(v_reuseFailAlloc_4128_, 1, v_cache_4098_);
lean_ctor_set(v_reuseFailAlloc_4128_, 2, v_zetaDeltaFVarIds_4099_);
lean_ctor_set(v_reuseFailAlloc_4128_, 3, v_postponed_4100_);
lean_ctor_set(v_reuseFailAlloc_4128_, 4, v_diag_4101_);
v___x_4125_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = lean_st_ref_put(v___y_4094_, v___x_4125_);
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4120_);
return v___x_4127_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4092_ = stack[0].m_obj;
lean_object* v_val_4093_ = stack[1].m_obj;
lean_object* v___y_4094_ = stack[2].m_obj;
lean_object* v_res_4132_;
v_res_4132_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4092_, v_val_4093_, v___y_4094_);
stack->m_obj
 = v_res_4132_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4133_, lean_object* v_val_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4133_, v_val_4134_, v___y_4135_);
lean_dec(v___y_4135_);
return v_res_4137_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4140_, uint8_t v_elimTrivial_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_lctx_4147_; lean_object* v___x_4148_; 
v_lctx_4147_ = lean_ctor_get(v___y_4142_, 2);
lean_inc(v_mvar_4140_);
v___x_4148_ = l_Lean_MVarId_getType(v_mvar_4140_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4148_, 1);
v___x_4150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4151_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4149_, v___x_4150_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v_fst_4153_; lean_object* v_snd_4154_; lean_object* v___x_4155_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v_fst_4153_ = lean_ctor_get(v_a_4152_, 0);
lean_inc(v_fst_4153_);
v_snd_4154_ = lean_ctor_get(v_a_4152_, 1);
lean_inc(v_snd_4154_);
lean_dec(v_a_4152_);
lean_inc_ref(v_lctx_4147_);
v___x_4155_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4147_, v_snd_4154_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4157_; lean_object* v_decls_4158_; lean_object* v___x_4159_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
v___x_4157_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4158_ = lean_ctor_get(v_a_4156_, 1);
lean_inc_ref(v_decls_4158_);
lean_dec(v_a_4156_);
v___x_4159_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4141_, v_decls_4158_, v___x_4157_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
lean_dec_ref(v_decls_4158_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v_fst_4161_; lean_object* v_snd_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
v_fst_4161_ = lean_ctor_get(v_a_4160_, 0);
lean_inc(v_fst_4161_);
v_snd_4162_ = lean_ctor_get(v_a_4160_, 1);
lean_inc(v_snd_4162_);
lean_dec(v_a_4160_);
v___x_4163_ = l_Lean_Expr_replaceFVars(v_fst_4153_, v_fst_4161_, v_snd_4162_);
lean_dec(v_snd_4162_);
lean_dec(v_fst_4153_);
v___x_4164_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4163_, v_elimTrivial_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4166_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
lean_inc(v_mvar_4140_);
v___x_4166_ = l_Lean_MVarId_getTag(v_mvar_4140_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4168_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v___x_4168_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4165_, v_a_4167_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; size_t v_sz_4172_; size_t v___x_4173_; lean_object* v___x_4174_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
lean_inc_n(v_a_4169_, 2);
lean_dec_ref_known(v___x_4168_, 1);
v___x_4170_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4140_, v_a_4169_, v___y_4143_);
lean_dec_ref(v___x_4170_);
v___x_4171_ = l_Lean_Expr_mvarId_x21(v_a_4169_);
lean_dec(v_a_4169_);
v_sz_4172_ = lean_array_size(v_fst_4161_);
v___x_4173_ = ((size_t)0ULL);
v___x_4174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4161_, v_sz_4172_, v___x_4173_, v___x_4171_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
lean_dec_ref(v___y_4142_);
lean_dec(v_fst_4161_);
return v___x_4174_;
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_dec(v_fst_4161_);
lean_dec_ref(v___y_4142_);
lean_dec(v_mvar_4140_);
v_a_4175_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4168_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4168_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
lean_dec(v_a_4165_);
lean_dec(v_fst_4161_);
lean_dec_ref(v___y_4142_);
lean_dec(v_mvar_4140_);
v_a_4183_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4166_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4166_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
lean_dec(v_fst_4161_);
lean_dec_ref(v___y_4142_);
lean_dec(v_mvar_4140_);
v_a_4191_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4164_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4164_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
lean_dec(v_fst_4153_);
lean_dec_ref(v___y_4142_);
lean_dec(v_mvar_4140_);
v_a_4199_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4159_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4159_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec(v_fst_4153_);
lean_dec_ref(v___y_4142_);
lean_dec(v_mvar_4140_);
v_a_4207_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4155_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4155_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
lean_dec_ref(v___y_4142_);
lean_dec(v_mvar_4140_);
v_a_4215_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4151_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4151_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec_ref(v___y_4142_);
lean_dec(v_mvar_4140_);
v_a_4223_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4148_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4148_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elimLets___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_4140_ = stack[0].m_obj;
uint8_t v_elimTrivial_4141_ = stack[1].m_num;
lean_object* v___y_4142_ = stack[2].m_obj;
lean_object* v___y_4143_ = stack[3].m_obj;
lean_object* v___y_4144_ = stack[4].m_obj;
lean_object* v___y_4145_ = stack[5].m_obj;
lean_object* v_res_4231_;
v_res_4231_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4140_, v_elimTrivial_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
stack->m_obj
 = v_res_4231_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4232_, lean_object* v_elimTrivial_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
uint8_t v_elimTrivial_boxed_4239_; lean_object* v_res_4240_; 
v_elimTrivial_boxed_4239_ = lean_unbox(v_elimTrivial_4233_);
v_res_4240_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4232_, v_elimTrivial_boxed_4239_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
return v_res_4240_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4241_, uint8_t v_elimTrivial_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v___x_4248_; lean_object* v___f_4249_; lean_object* v___x_4250_; 
v___x_4248_ = lean_box(v_elimTrivial_4242_);
lean_inc(v_mvar_4241_);
v___f_4249_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4249_, 0, v_mvar_4241_);
lean_closure_set(v___f_4249_, 1, v___x_4248_);
v___x_4250_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4241_, v___f_4249_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
return v___x_4250_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_elimLets_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_4241_ = stack[0].m_obj;
uint8_t v_elimTrivial_4242_ = stack[1].m_num;
lean_object* v_a_4243_ = stack[2].m_obj;
lean_object* v_a_4244_ = stack[3].m_obj;
lean_object* v_a_4245_ = stack[4].m_obj;
lean_object* v_a_4246_ = stack[5].m_obj;
lean_object* v_res_4251_;
v_res_4251_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4241_, v_elimTrivial_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
stack->m_obj
 = v_res_4251_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4252_, lean_object* v_elimTrivial_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_){
_start:
{
uint8_t v_elimTrivial_boxed_4259_; lean_object* v_res_4260_; 
v_elimTrivial_boxed_4259_ = lean_unbox(v_elimTrivial_4253_);
v_res_4260_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4252_, v_elimTrivial_boxed_4259_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_);
lean_dec(v_a_4257_);
lean_dec_ref(v_a_4256_);
lean_dec(v_a_4255_);
lean_dec_ref(v_a_4254_);
return v_res_4260_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4261_, lean_object* v_val_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4261_, v_val_4262_, v___y_4264_);
return v___x_4268_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4261_ = stack[0].m_obj;
lean_object* v_val_4262_ = stack[1].m_obj;
lean_object* v___y_4263_ = stack[2].m_obj;
lean_object* v___y_4264_ = stack[3].m_obj;
lean_object* v___y_4265_ = stack[4].m_obj;
lean_object* v___y_4266_ = stack[5].m_obj;
lean_object* v_res_4269_;
v_res_4269_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4261_, v_val_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
stack->m_obj
 = v_res_4269_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4270_, lean_object* v_val_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4270_, v_val_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4278_, lean_object* v_x_4279_, lean_object* v_x_4280_, lean_object* v_x_4281_){
_start:
{
lean_object* v___x_4282_; 
v___x_4282_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4279_, v_x_4280_, v_x_4281_);
return v___x_4282_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4283_, lean_object* v_as_4284_, size_t v_sz_4285_, size_t v_i_4286_, lean_object* v_b_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4283_, v_as_4284_, v_sz_4285_, v_i_4286_, v_b_4287_);
return v___x_4293_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_elimTrivial_4283_ = stack[0].m_num;
lean_object* v_as_4284_ = stack[1].m_obj;
size_t v_sz_4285_ = stack[2].m_num;
size_t v_i_4286_ = stack[3].m_num;
lean_object* v_b_4287_ = stack[4].m_obj;
lean_object* v___y_4288_ = stack[5].m_obj;
lean_object* v___y_4289_ = stack[6].m_obj;
lean_object* v___y_4290_ = stack[7].m_obj;
lean_object* v___y_4291_ = stack[8].m_obj;
lean_object* v_res_4294_;
v_res_4294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_4283_, v_as_4284_, v_sz_4285_, v_i_4286_, v_b_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
stack->m_obj
 = v_res_4294_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4295_, lean_object* v_as_4296_, lean_object* v_sz_4297_, lean_object* v_i_4298_, lean_object* v_b_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
uint8_t v_elimTrivial_boxed_4305_; size_t v_sz_boxed_4306_; size_t v_i_boxed_4307_; lean_object* v_res_4308_; 
v_elimTrivial_boxed_4305_ = lean_unbox(v_elimTrivial_4295_);
v_sz_boxed_4306_ = lean_unbox_usize(v_sz_4297_);
lean_dec(v_sz_4297_);
v_i_boxed_4307_ = lean_unbox_usize(v_i_4298_);
lean_dec(v_i_4298_);
v_res_4308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4305_, v_as_4296_, v_sz_boxed_4306_, v_i_boxed_4307_, v_b_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec_ref(v_as_4296_);
return v_res_4308_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4309_, lean_object* v_x_4310_, size_t v_x_4311_, size_t v_x_4312_, lean_object* v_x_4313_, lean_object* v_x_4314_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4310_, v_x_4311_, v_x_4312_, v_x_4313_, v_x_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4310_ = stack[1].m_obj;
size_t v_x_4311_ = stack[2].m_num;
size_t v_x_4312_ = stack[3].m_num;
lean_object* v_x_4313_ = stack[4].m_obj;
lean_object* v_x_4314_ = stack[5].m_obj;
lean_object* v_res_4316_;
v_res_4316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_box(0), v_x_4310_, v_x_4311_, v_x_4312_, v_x_4313_, v_x_4314_);
stack->m_obj
 = v_res_4316_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4317_, lean_object* v_x_4318_, lean_object* v_x_4319_, lean_object* v_x_4320_, lean_object* v_x_4321_, lean_object* v_x_4322_){
_start:
{
size_t v_x_8968__boxed_4323_; size_t v_x_8969__boxed_4324_; lean_object* v_res_4325_; 
v_x_8968__boxed_4323_ = lean_unbox_usize(v_x_4319_);
lean_dec(v_x_4319_);
v_x_8969__boxed_4324_ = lean_unbox_usize(v_x_4320_);
lean_dec(v_x_4320_);
v_res_4325_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4317_, v_x_4318_, v_x_8968__boxed_4323_, v_x_8969__boxed_4324_, v_x_4321_, v_x_4322_);
return v_res_4325_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4326_, lean_object* v_as_4327_, size_t v_sz_4328_, size_t v_i_4329_, lean_object* v_b_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4326_, v_as_4327_, v_sz_4328_, v_i_4329_, v_b_4330_);
return v___x_4336_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
uint8_t v_elimTrivial_4326_ = stack[0].m_num;
lean_object* v_as_4327_ = stack[1].m_obj;
size_t v_sz_4328_ = stack[2].m_num;
size_t v_i_4329_ = stack[3].m_num;
lean_object* v_b_4330_ = stack[4].m_obj;
lean_object* v___y_4331_ = stack[5].m_obj;
lean_object* v___y_4332_ = stack[6].m_obj;
lean_object* v___y_4333_ = stack[7].m_obj;
lean_object* v___y_4334_ = stack[8].m_obj;
lean_object* v_res_4337_;
v_res_4337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_4326_, v_as_4327_, v_sz_4328_, v_i_4329_, v_b_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_);
stack->m_obj
 = v_res_4337_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4338_, lean_object* v_as_4339_, lean_object* v_sz_4340_, lean_object* v_i_4341_, lean_object* v_b_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
uint8_t v_elimTrivial_boxed_4348_; size_t v_sz_boxed_4349_; size_t v_i_boxed_4350_; lean_object* v_res_4351_; 
v_elimTrivial_boxed_4348_ = lean_unbox(v_elimTrivial_4338_);
v_sz_boxed_4349_ = lean_unbox_usize(v_sz_4340_);
lean_dec(v_sz_4340_);
v_i_boxed_4350_ = lean_unbox_usize(v_i_4341_);
lean_dec(v_i_4341_);
v_res_4351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4348_, v_as_4339_, v_sz_boxed_4349_, v_i_boxed_4350_, v_b_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec_ref(v_as_4339_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4352_, lean_object* v_n_4353_, lean_object* v_k_4354_, lean_object* v_v_4355_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4353_, v_k_4354_, v_v_4355_);
return v___x_4356_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4357_, size_t v_depth_4358_, lean_object* v_keys_4359_, lean_object* v_vals_4360_, lean_object* v_heq_4361_, lean_object* v_i_4362_, lean_object* v_entries_4363_){
_start:
{
lean_object* v___x_4364_; 
v___x_4364_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4358_, v_keys_4359_, v_vals_4360_, v_i_4362_, v_entries_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12_0interp(lean_interpreter_value* stack)
{
size_t v_depth_4358_ = stack[1].m_num;
lean_object* v_keys_4359_ = stack[2].m_obj;
lean_object* v_vals_4360_ = stack[3].m_obj;
lean_object* v_i_4362_ = stack[5].m_obj;
lean_object* v_entries_4363_ = stack[6].m_obj;
lean_object* v_res_4365_;
v_res_4365_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_box(0), v_depth_4358_, v_keys_4359_, v_vals_4360_, lean_box(0), v_i_4362_, v_entries_4363_);
stack->m_obj
 = v_res_4365_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4366_, lean_object* v_depth_4367_, lean_object* v_keys_4368_, lean_object* v_vals_4369_, lean_object* v_heq_4370_, lean_object* v_i_4371_, lean_object* v_entries_4372_){
_start:
{
size_t v_depth_boxed_4373_; lean_object* v_res_4374_; 
v_depth_boxed_4373_ = lean_unbox_usize(v_depth_4367_);
lean_dec(v_depth_4367_);
v_res_4374_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4366_, v_depth_boxed_4373_, v_keys_4368_, v_vals_4369_, v_heq_4370_, v_i_4371_, v_entries_4372_);
lean_dec_ref(v_vals_4369_);
lean_dec_ref(v_keys_4368_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4375_, lean_object* v_x_4376_, lean_object* v_x_4377_, lean_object* v_x_4378_, lean_object* v_x_4379_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4376_, v_x_4377_, v_x_4378_, v_x_4379_);
return v___x_4380_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_instInhabitedUses_default = _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default();
l_Lean_Elab_Tactic_Do_instInhabitedUses = _init_l_Lean_Elab_Tactic_Do_instInhabitedUses();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1 = _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
}
#ifdef __cplusplus
}
#endif
