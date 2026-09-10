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
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uses"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 67, 224, 192, 49, 118, 23, 147)}};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3;
static const lean_closure_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_boxed_6_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(lean_object* v_zero_23_){
_start:
{
lean_inc(v_zero_23_);
return v_zero_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(lean_object* v_zero_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(v_zero_24_);
lean_dec(v_zero_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_zero_29_){
_start:
{
lean_inc(v_zero_29_);
return v_zero_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_zero_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_zero_33_);
lean_dec(v_zero_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(lean_object* v_one_36_){
_start:
{
lean_inc(v_one_36_);
return v_one_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(lean_object* v_one_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(v_one_37_);
lean_dec(v_one_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_one_42_){
_start:
{
lean_inc(v_one_42_);
return v_one_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_one_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Elab_Tactic_Do_Uses_one_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_one_46_);
lean_dec(v_one_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(lean_object* v_many_49_){
_start:
{
lean_inc(v_many_49_);
return v_many_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(lean_object* v_many_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(v_many_50_);
lean_dec(v_many_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_many_55_){
_start:
{
lean_inc(v_many_55_);
return v_many_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_many_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Elab_Tactic_Do_Uses_many_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_many_59_);
lean_dec(v_many_59_);
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instBEqUses_beq(uint8_t v_x_62_, uint8_t v_y_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_64_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_62_);
v___x_65_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_63_);
v___x_66_ = lean_nat_dec_eq(v___x_64_, v___x_65_);
lean_dec(v___x_65_);
lean_dec(v___x_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(lean_object* v_x_67_, lean_object* v_y_68_){
_start:
{
uint8_t v_x_21__boxed_69_; uint8_t v_y_22__boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v_x_21__boxed_69_ = lean_unbox(v_x_67_);
v_y_22__boxed_70_ = lean_unbox(v_y_68_);
v_res_71_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_x_21__boxed_69_, v_y_22__boxed_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instOrdUses_ord(uint8_t v_x_75_, uint8_t v_y_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_75_);
v___x_78_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_76_);
v___x_79_ = lean_nat_dec_lt(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
uint8_t v___x_80_; 
v___x_80_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
lean_dec(v___x_78_);
lean_dec(v___x_77_);
if (v___x_80_ == 0)
{
uint8_t v___x_81_; 
v___x_81_ = 2;
return v___x_81_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 1;
return v___x_82_;
}
}
else
{
uint8_t v___x_83_; 
lean_dec(v___x_78_);
lean_dec(v___x_77_);
v___x_83_ = 0;
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(lean_object* v_x_84_, lean_object* v_y_85_){
_start:
{
uint8_t v_x_30__boxed_86_; uint8_t v_y_31__boxed_87_; uint8_t v_res_88_; lean_object* v_r_89_; 
v_x_30__boxed_86_ = lean_unbox(v_x_84_);
v_y_31__boxed_87_ = lean_unbox(v_y_85_);
v_res_88_ = l_Lean_Elab_Tactic_Do_instOrdUses_ord(v_x_30__boxed_86_, v_y_31__boxed_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default(void){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses(void){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_add(uint8_t v_x_94_, uint8_t v_x_95_){
_start:
{
if (v_x_94_ == 0)
{
return v_x_95_;
}
else
{
if (v_x_95_ == 0)
{
return v_x_94_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 2;
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_add___boxed(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_x_18__boxed_99_; uint8_t v_x_19__boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_x_18__boxed_99_ = lean_unbox(v_x_97_);
v_x_19__boxed_100_ = lean_unbox(v_x_98_);
v_res_101_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x_18__boxed_99_, v_x_19__boxed_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat(uint8_t v_x_103_){
_start:
{
switch(v_x_103_)
{
case 0:
{
lean_object* v___x_104_; 
v___x_104_ = lean_unsigned_to_nat(0u);
return v___x_104_;
}
case 1:
{
lean_object* v___x_105_; 
v___x_105_ = lean_unsigned_to_nat(1u);
return v___x_105_;
}
default: 
{
lean_object* v___x_106_; 
v___x_106_ = lean_unsigned_to_nat(2u);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(lean_object* v_x_107_){
_start:
{
uint8_t v_x_34__boxed_108_; lean_object* v_res_109_; 
v_x_34__boxed_108_ = lean_unbox(v_x_107_);
v_res_109_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v_x_34__boxed_108_);
return v_res_109_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_fromNat(lean_object* v_x_110_){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_nat_dec_eq(v_x_110_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_dec_eq(v_x_110_, v___x_113_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = 2;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 1;
return v___x_116_;
}
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(lean_object* v_x_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v_x_118_);
lean_dec(v_x_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_124_) == 0)
{
return v_x_123_;
}
else
{
lean_object* v_key_125_; lean_object* v_value_126_; lean_object* v_tail_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_150_; 
v_key_125_ = lean_ctor_get(v_x_124_, 0);
v_value_126_ = lean_ctor_get(v_x_124_, 1);
v_tail_127_ = lean_ctor_get(v_x_124_, 2);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_124_);
if (v_isSharedCheck_150_ == 0)
{
v___x_129_ = v_x_124_;
v_isShared_130_ = v_isSharedCheck_150_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_tail_127_);
lean_inc(v_value_126_);
lean_inc(v_key_125_);
lean_dec(v_x_124_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_150_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v_fold_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_131_ = lean_array_get_size(v_x_123_);
v___x_132_ = l_Lean_instHashableFVarId_hash(v_key_125_);
v___x_133_ = 32ULL;
v___x_134_ = lean_uint64_shift_right(v___x_132_, v___x_133_);
v_fold_135_ = lean_uint64_xor(v___x_132_, v___x_134_);
v___x_136_ = 16ULL;
v___x_137_ = lean_uint64_shift_right(v_fold_135_, v___x_136_);
v___x_138_ = lean_uint64_xor(v_fold_135_, v___x_137_);
v___x_139_ = lean_uint64_to_usize(v___x_138_);
v___x_140_ = lean_usize_of_nat(v___x_131_);
v___x_141_ = ((size_t)1ULL);
v___x_142_ = lean_usize_sub(v___x_140_, v___x_141_);
v___x_143_ = lean_usize_land(v___x_139_, v___x_142_);
v___x_144_ = lean_array_uget_borrowed(v_x_123_, v___x_143_);
lean_inc(v___x_144_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 2, v___x_144_);
v___x_146_ = v___x_129_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_key_125_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_value_126_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v___x_144_);
v___x_146_ = v_reuseFailAlloc_149_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_array_uset(v_x_123_, v___x_143_, v___x_146_);
v_x_123_ = v___x_147_;
v_x_124_ = v_tail_127_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(lean_object* v_i_151_, lean_object* v_source_152_, lean_object* v_target_153_){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_array_get_size(v_source_152_);
v___x_155_ = lean_nat_dec_lt(v_i_151_, v___x_154_);
if (v___x_155_ == 0)
{
lean_dec_ref(v_source_152_);
lean_dec(v_i_151_);
return v_target_153_;
}
else
{
lean_object* v_es_156_; lean_object* v___x_157_; lean_object* v_source_158_; lean_object* v_target_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_es_156_ = lean_array_fget(v_source_152_, v_i_151_);
v___x_157_ = lean_box(0);
v_source_158_ = lean_array_fset(v_source_152_, v_i_151_, v___x_157_);
v_target_159_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_target_153_, v_es_156_);
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_add(v_i_151_, v___x_160_);
lean_dec(v_i_151_);
v_i_151_ = v___x_161_;
v_source_152_ = v_source_158_;
v_target_153_ = v_target_159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(lean_object* v_data_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_nbuckets_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_164_ = lean_array_get_size(v_data_163_);
v___x_165_ = lean_unsigned_to_nat(2u);
v_nbuckets_166_ = lean_nat_mul(v___x_164_, v___x_165_);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_box(0);
v___x_169_ = lean_mk_array(v_nbuckets_166_, v___x_168_);
v___x_170_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v___x_167_, v_data_163_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object* v_a_171_, lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
uint8_t v___x_173_; 
v___x_173_ = 0;
return v___x_173_;
}
else
{
lean_object* v_key_174_; lean_object* v_tail_175_; uint8_t v___x_176_; 
v_key_174_ = lean_ctor_get(v_x_172_, 0);
v_tail_175_ = lean_ctor_get(v_x_172_, 2);
v___x_176_ = l_Lean_instBEqFVarId_beq(v_key_174_, v_a_171_);
if (v___x_176_ == 0)
{
v_x_172_ = v_tail_175_;
goto _start;
}
else
{
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_178_, v_x_179_);
lean_dec(v_x_179_);
lean_dec(v_a_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(uint8_t v_x3_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_box(v_x3_182_);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
else
{
lean_object* v_val_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_196_; 
v_val_186_ = lean_ctor_get(v_x_183_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_196_ == 0)
{
v___x_188_ = v_x_183_;
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_val_186_);
lean_dec(v_x_183_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_196_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
uint8_t v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_190_ = lean_unbox(v_val_186_);
lean_dec(v_val_186_);
v___x_191_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x3_182_, v___x_190_);
v___x_192_ = lean_box(v___x_191_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_192_);
v___x_194_ = v___x_188_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(lean_object* v_x3_197_, lean_object* v_x_198_){
_start:
{
uint8_t v_x3_851__boxed_199_; lean_object* v_res_200_; 
v_x3_851__boxed_199_ = lean_unbox(v_x3_197_);
v_res_200_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_851__boxed_199_, v_x_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(uint8_t v_x3_201_, lean_object* v_a_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_val_206_; lean_object* v___x_207_; 
v___x_204_ = lean_box(0);
v___x_205_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_201_, v___x_204_);
v_val_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_206_);
lean_dec(v___x_205_);
v___x_207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_207_, 0, v_a_202_);
lean_ctor_set(v___x_207_, 1, v_val_206_);
lean_ctor_set(v___x_207_, 2, v_x_203_);
return v___x_207_;
}
else
{
lean_object* v_key_208_; lean_object* v_value_209_; lean_object* v_tail_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_225_; 
v_key_208_ = lean_ctor_get(v_x_203_, 0);
v_value_209_ = lean_ctor_get(v_x_203_, 1);
v_tail_210_ = lean_ctor_get(v_x_203_, 2);
v_isSharedCheck_225_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_225_ == 0)
{
v___x_212_ = v_x_203_;
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_tail_210_);
lean_inc(v_value_209_);
lean_inc(v_key_208_);
lean_dec(v_x_203_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
uint8_t v___x_214_; 
v___x_214_ = l_Lean_instBEqFVarId_beq(v_key_208_, v_a_202_);
if (v___x_214_ == 0)
{
lean_object* v_tail_215_; lean_object* v___x_217_; 
v_tail_215_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_201_, v_a_202_, v_tail_210_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 2, v_tail_215_);
v___x_217_ = v___x_212_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_key_208_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_value_209_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_tail_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_val_221_; lean_object* v___x_223_; 
lean_dec(v_key_208_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v_value_209_);
v___x_220_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_201_, v___x_219_);
v_val_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_221_);
lean_dec(v___x_220_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v_val_221_);
lean_ctor_set(v___x_212_, 0, v_a_202_);
v___x_223_ = v___x_212_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_202_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_val_221_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_tail_210_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(lean_object* v_x3_226_, lean_object* v_a_227_, lean_object* v_x_228_){
_start:
{
uint8_t v_x3_883__boxed_229_; lean_object* v_res_230_; 
v_x3_883__boxed_229_ = lean_unbox(v_x3_226_);
v_res_230_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_883__boxed_229_, v_a_227_, v_x_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(uint8_t v_x3_231_, lean_object* v_m_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_size_234_; lean_object* v_buckets_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_284_; 
v_size_234_ = lean_ctor_get(v_m_232_, 0);
v_buckets_235_ = lean_ctor_get(v_m_232_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_m_232_);
if (v_isSharedCheck_284_ == 0)
{
v___x_237_ = v_m_232_;
v_isShared_238_ = v_isSharedCheck_284_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_buckets_235_);
lean_inc(v_size_234_);
lean_dec(v_m_232_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_284_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v_fold_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v_bkt_252_; uint8_t v___x_253_; 
v___x_239_ = lean_array_get_size(v_buckets_235_);
v___x_240_ = l_Lean_instHashableFVarId_hash(v_a_233_);
v___x_241_ = 32ULL;
v___x_242_ = lean_uint64_shift_right(v___x_240_, v___x_241_);
v_fold_243_ = lean_uint64_xor(v___x_240_, v___x_242_);
v___x_244_ = 16ULL;
v___x_245_ = lean_uint64_shift_right(v_fold_243_, v___x_244_);
v___x_246_ = lean_uint64_xor(v_fold_243_, v___x_245_);
v___x_247_ = lean_uint64_to_usize(v___x_246_);
v___x_248_ = lean_usize_of_nat(v___x_239_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_sub(v___x_248_, v___x_249_);
v___x_251_ = lean_usize_land(v___x_247_, v___x_250_);
v_bkt_252_ = lean_array_uget_borrowed(v_buckets_235_, v___x_251_);
v___x_253_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_233_, v_bkt_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v_size_x27_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_buckets_x27_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_254_ = lean_unsigned_to_nat(1u);
v_size_x27_255_ = lean_nat_add(v_size_234_, v___x_254_);
lean_dec(v_size_234_);
v___x_256_ = lean_box(v_x3_231_);
lean_inc(v_bkt_252_);
v___x_257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_257_, 0, v_a_233_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
lean_ctor_set(v___x_257_, 2, v_bkt_252_);
v_buckets_x27_258_ = lean_array_uset(v_buckets_235_, v___x_251_, v___x_257_);
v___x_259_ = lean_unsigned_to_nat(4u);
v___x_260_ = lean_nat_mul(v_size_x27_255_, v___x_259_);
v___x_261_ = lean_unsigned_to_nat(3u);
v___x_262_ = lean_nat_div(v___x_260_, v___x_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_array_get_size(v_buckets_x27_258_);
v___x_264_ = lean_nat_dec_le(v___x_262_, v___x_263_);
lean_dec(v___x_262_);
if (v___x_264_ == 0)
{
lean_object* v_val_265_; lean_object* v___x_267_; 
v_val_265_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_258_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_val_265_);
lean_ctor_set(v___x_237_, 0, v_size_x27_255_);
v___x_267_ = v___x_237_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_size_x27_255_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_val_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
else
{
lean_object* v___x_270_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_buckets_x27_258_);
lean_ctor_set(v___x_237_, 0, v_size_x27_255_);
v___x_270_ = v___x_237_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_size_x27_255_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_buckets_x27_258_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
else
{
lean_object* v___x_272_; lean_object* v_buckets_x27_273_; lean_object* v_bkt_x27_274_; lean_object* v___y_276_; uint8_t v___x_281_; 
lean_inc(v_bkt_252_);
v___x_272_ = lean_box(0);
v_buckets_x27_273_ = lean_array_uset(v_buckets_235_, v___x_251_, v___x_272_);
lean_inc(v_a_233_);
v_bkt_x27_274_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_231_, v_a_233_, v_bkt_252_);
v___x_281_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_233_, v_bkt_x27_274_);
lean_dec(v_a_233_);
if (v___x_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_sub(v_size_234_, v___x_282_);
lean_dec(v_size_234_);
v___y_276_ = v___x_283_;
goto v___jp_275_;
}
else
{
v___y_276_ = v_size_234_;
goto v___jp_275_;
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_array_uset(v_buckets_x27_273_, v___x_251_, v_bkt_x27_274_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_277_);
lean_ctor_set(v___x_237_, 0, v___y_276_);
v___x_279_ = v___x_237_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___y_276_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object* v_x3_285_, lean_object* v_m_286_, lean_object* v_a_287_){
_start:
{
uint8_t v_x3_931__boxed_288_; lean_object* v_res_289_; 
v_x3_931__boxed_288_ = lean_unbox(v_x3_285_);
v_res_289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v_x3_931__boxed_288_, v_m_286_, v_a_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
return v_x_290_;
}
else
{
lean_object* v_key_292_; lean_object* v_value_293_; lean_object* v_tail_294_; uint8_t v___x_295_; lean_object* v___x_296_; 
v_key_292_ = lean_ctor_get(v_x_291_, 0);
lean_inc(v_key_292_);
v_value_293_ = lean_ctor_get(v_x_291_, 1);
lean_inc(v_value_293_);
v_tail_294_ = lean_ctor_get(v_x_291_, 2);
lean_inc(v_tail_294_);
lean_dec_ref_known(v_x_291_, 3);
v___x_295_ = lean_unbox(v_value_293_);
lean_dec(v_value_293_);
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v___x_295_, v_x_290_, v_key_292_);
v_x_290_ = v___x_296_;
v_x_291_ = v_tail_294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object* v_as_298_, size_t v_i_299_, size_t v_stop_300_, lean_object* v_b_301_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = lean_usize_dec_eq(v_i_299_, v_stop_300_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; size_t v___x_305_; size_t v___x_306_; 
v___x_303_ = lean_array_uget_borrowed(v_as_298_, v_i_299_);
lean_inc(v___x_303_);
v___x_304_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(v_b_301_, v___x_303_);
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_add(v_i_299_, v___x_305_);
v_i_299_ = v___x_306_;
v_b_301_ = v___x_304_;
goto _start;
}
else
{
return v_b_301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object* v_as_308_, lean_object* v_i_309_, lean_object* v_stop_310_, lean_object* v_b_311_){
_start:
{
size_t v_i_boxed_312_; size_t v_stop_boxed_313_; lean_object* v_res_314_; 
v_i_boxed_312_ = lean_unbox_usize(v_i_309_);
lean_dec(v_i_309_);
v_stop_boxed_313_ = lean_unbox_usize(v_stop_310_);
lean_dec(v_stop_310_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_as_308_, v_i_boxed_312_, v_stop_boxed_313_, v_b_311_);
lean_dec_ref(v_as_308_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object* v_a_315_, lean_object* v_b_316_){
_start:
{
lean_object* v_buckets_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v_buckets_317_ = lean_ctor_get(v_a_315_, 1);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_array_get_size(v_buckets_317_);
v___x_320_ = lean_nat_dec_lt(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
return v_b_316_;
}
else
{
size_t v___x_321_; size_t v___x_322_; lean_object* v___x_323_; 
v___x_321_ = ((size_t)0ULL);
v___x_322_ = lean_usize_of_nat(v___x_319_);
v___x_323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_317_, v___x_321_, v___x_322_, v_b_316_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object* v_a_324_, lean_object* v_b_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_a_324_, v_b_325_);
lean_dec_ref(v_a_324_);
return v_res_326_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object* v_00_u03b2_327_, lean_object* v_a_328_, lean_object* v_x_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_328_, v_x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_331_, lean_object* v_a_332_, lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(v_00_u03b2_331_, v_a_332_, v_x_333_);
lean_dec(v_x_333_);
lean_dec(v_a_332_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(lean_object* v_00_u03b2_336_, lean_object* v_data_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_data_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_339_, lean_object* v_i_340_, lean_object* v_source_341_, lean_object* v_target_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v_i_340_, v_source_341_, v_target_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_x_345_, v_x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v___x_351_; 
v___x_351_ = lean_unsigned_to_nat(0u);
return v___x_351_;
}
else
{
lean_object* v___x_352_; 
v___x_352_ = lean_unsigned_to_nat(1u);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg___boxed(lean_object* v_x_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_353_);
lean_dec(v_x_353_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(lean_object* v_n_355_, lean_object* v_x_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___boxed(lean_object* v_n_358_, lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(v_n_358_, v_x_359_);
lean_dec(v_x_359_);
lean_dec(v_n_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object* v_t_361_, lean_object* v_k_362_){
_start:
{
if (lean_obj_tag(v_t_361_) == 0)
{
return v_k_362_;
}
else
{
lean_object* v_uses_363_; lean_object* v___x_364_; 
v_uses_363_ = lean_ctor_get(v_t_361_, 0);
lean_inc_ref(v_uses_363_);
lean_dec_ref_known(v_t_361_, 1);
v___x_364_ = lean_apply_1(v_k_362_, v_uses_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object* v_n_365_, lean_object* v_motive_366_, lean_object* v_ctorIdx_367_, lean_object* v_t_368_, lean_object* v_h_369_, lean_object* v_k_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_368_, v_k_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object* v_n_372_, lean_object* v_motive_373_, lean_object* v_ctorIdx_374_, lean_object* v_t_375_, lean_object* v_h_376_, lean_object* v_k_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(v_n_372_, v_motive_373_, v_ctorIdx_374_, v_t_375_, v_h_376_, v_k_377_);
lean_dec(v_ctorIdx_374_);
lean_dec(v_n_372_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object* v_t_379_, lean_object* v_none_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_379_, v_none_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object* v_n_382_, lean_object* v_motive_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_none_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_384_, v_none_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object* v_n_388_, lean_object* v_motive_389_, lean_object* v_t_390_, lean_object* v_h_391_, lean_object* v_none_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Elab_Tactic_Do_BVarUses_none_elim(v_n_388_, v_motive_389_, v_t_390_, v_h_391_, v_none_392_);
lean_dec(v_n_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object* v_t_394_, lean_object* v_some_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_394_, v_some_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object* v_n_397_, lean_object* v_motive_398_, lean_object* v_t_399_, lean_object* v_h_400_, lean_object* v_some_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_399_, v_some_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object* v_n_403_, lean_object* v_motive_404_, lean_object* v_t_405_, lean_object* v_h_406_, lean_object* v_some_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Elab_Tactic_Do_BVarUses_some_elim(v_n_403_, v_motive_404_, v_t_405_, v_h_406_, v_some_407_);
lean_dec(v_n_403_);
return v_res_408_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12));
v___x_434_ = l_Lean_mkAtom(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13);
v___x_436_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_437_ = lean_array_push(v___x_436_, v___x_435_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_438_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14);
v___x_439_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11));
v___x_440_ = lean_box(2);
v___x_441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_438_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15);
v___x_443_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_444_ = lean_array_push(v___x_443_, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_445_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16);
v___x_446_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9));
v___x_447_ = lean_box(2);
v___x_448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_446_);
lean_ctor_set(v___x_448_, 2, v___x_445_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17);
v___x_450_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_451_ = lean_array_push(v___x_450_, v___x_449_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_452_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18);
v___x_453_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7));
v___x_454_ = lean_box(2);
v___x_455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_453_);
lean_ctor_set(v___x_455_, 2, v___x_452_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19);
v___x_457_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_458_ = lean_array_push(v___x_457_, v___x_456_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_459_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20);
v___x_460_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4));
v___x_461_ = lean_box(2);
v___x_462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
lean_ctor_set(v___x_462_, 2, v___x_459_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1(void){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21);
return v___x_463_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object* v_numBVars_464_, lean_object* v_n_465_, lean_object* v_i_466_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_sub(v_numBVars_464_, v___x_467_);
v___x_469_ = lean_nat_sub(v___x_468_, v_n_465_);
lean_dec(v___x_468_);
v___x_470_ = lean_nat_dec_eq(v_i_466_, v___x_469_);
lean_dec(v___x_469_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
v___x_471_ = 0;
return v___x_471_;
}
else
{
uint8_t v___x_472_; 
v___x_472_ = 1;
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object* v_numBVars_473_, lean_object* v_n_474_, lean_object* v_i_475_){
_start:
{
uint8_t v_res_476_; lean_object* v_r_477_; 
v_res_476_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(v_numBVars_473_, v_n_474_, v_i_475_);
lean_dec(v_i_475_);
lean_dec(v_n_474_);
lean_dec(v_numBVars_473_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object* v_numBVars_478_, lean_object* v_n_479_){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
lean_inc(v_numBVars_478_);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_480_, 0, v_numBVars_478_);
lean_closure_set(v___f_480_, 1, v_n_479_);
v___x_481_ = l_Array_ofFn___redArg(v_numBVars_478_, v___f_480_);
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object* v_numBVars_483_, lean_object* v_n_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(v_numBVars_483_, v_n_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object* v_numBVars_491_, lean_object* v_x_492_){
_start:
{
if (lean_obj_tag(v_x_492_) == 0)
{
lean_object* v___x_493_; 
v___x_493_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0));
return v___x_493_;
}
else
{
lean_object* v_uses_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_507_; 
v_uses_494_ = lean_ctor_get(v_x_492_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v_x_492_);
if (v_isSharedCheck_507_ == 0)
{
v___x_496_ = v_x_492_;
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_uses_494_);
lean_dec(v_x_492_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_add(v_numBVars_491_, v___x_498_);
v___x_500_ = lean_nat_sub(v___x_499_, v___x_498_);
lean_dec(v___x_499_);
v___x_501_ = lean_array_fget(v_uses_494_, v___x_500_);
lean_dec(v___x_500_);
v___x_502_ = lean_array_pop(v_uses_494_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_502_);
v___x_504_ = v___x_496_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_506_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; 
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_501_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
return v___x_505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object* v_numBVars_508_, lean_object* v_x_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Elab_Tactic_Do_BVarUses_pop(v_numBVars_508_, v_x_509_);
lean_dec(v_numBVars_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object* v_as_511_, lean_object* v_bs_512_, lean_object* v_i_513_, lean_object* v_cs_514_){
_start:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_array_get_size(v_as_511_);
v___x_516_ = lean_nat_dec_lt(v_i_513_, v___x_515_);
if (v___x_516_ == 0)
{
lean_dec(v_i_513_);
return v_cs_514_;
}
else
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_array_get_size(v_bs_512_);
v___x_518_ = lean_nat_dec_lt(v_i_513_, v___x_517_);
if (v___x_518_ == 0)
{
lean_dec(v_i_513_);
return v_cs_514_;
}
else
{
lean_object* v_a_519_; lean_object* v_b_520_; uint8_t v___x_521_; uint8_t v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_a_519_ = lean_array_fget_borrowed(v_as_511_, v_i_513_);
v_b_520_ = lean_array_fget_borrowed(v_bs_512_, v_i_513_);
v___x_521_ = lean_unbox(v_a_519_);
v___x_522_ = lean_unbox(v_b_520_);
v___x_523_ = l_Lean_Elab_Tactic_Do_Uses_add(v___x_521_, v___x_522_);
v___x_524_ = lean_unsigned_to_nat(1u);
v___x_525_ = lean_nat_add(v_i_513_, v___x_524_);
lean_dec(v_i_513_);
v___x_526_ = lean_box(v___x_523_);
v___x_527_ = lean_array_push(v_cs_514_, v___x_526_);
v_i_513_ = v___x_525_;
v_cs_514_ = v___x_527_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object* v_as_529_, lean_object* v_bs_530_, lean_object* v_i_531_, lean_object* v_cs_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_as_529_, v_bs_530_, v_i_531_, v_cs_532_);
lean_dec_ref(v_bs_530_);
lean_dec_ref(v_as_529_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
if (lean_obj_tag(v_a_536_) == 0)
{
return v_b_537_;
}
else
{
if (lean_obj_tag(v_b_537_) == 0)
{
lean_object* v_uses_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
v_uses_538_ = lean_ctor_get(v_a_536_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_536_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v_a_536_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_uses_538_);
lean_dec(v_a_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_uses_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
lean_object* v_uses_546_; lean_object* v_uses_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_557_; 
v_uses_546_ = lean_ctor_get(v_a_536_, 0);
lean_inc_ref(v_uses_546_);
lean_dec_ref_known(v_a_536_, 1);
v_uses_547_ = lean_ctor_get(v_b_537_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v_b_537_);
if (v_isSharedCheck_557_ == 0)
{
v___x_549_ = v_b_537_;
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_uses_547_);
lean_dec(v_b_537_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0));
v___x_553_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_uses_546_, v_uses_547_, v___x_551_, v___x_552_);
lean_dec_ref(v_uses_547_);
lean_dec_ref(v_uses_546_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_553_);
v___x_555_ = v___x_549_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object* v_numBVars_558_, lean_object* v_a_559_, lean_object* v_b_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(v_a_559_, v_b_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object* v_numBVars_562_, lean_object* v_a_563_, lean_object* v_b_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Elab_Tactic_Do_BVarUses_add(v_numBVars_562_, v_a_563_, v_b_564_);
lean_dec(v_numBVars_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object* v_numBVars_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_add___boxed), 3, 1);
lean_closure_set(v___x_567_, 0, v_numBVars_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object* v_f_568_, lean_object* v_x_569_){
_start:
{
lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
v_fst_570_ = lean_ctor_get(v_x_569_, 0);
v_snd_571_ = lean_ctor_get(v_x_569_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_569_);
if (v_isSharedCheck_579_ == 0)
{
v___x_573_ = v_x_569_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_snd_571_);
lean_inc(v_fst_570_);
lean_dec(v_x_569_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_575_ = lean_apply_1(v_f_568_, v_fst_570_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_snd_571_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object* v_00_u03b1_u2081_580_, lean_object* v_00_u03b1_u2082_581_, lean_object* v_00_u03b2_582_, lean_object* v_f_583_, lean_object* v_x_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v_f_583_, v_x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object* v_x_586_, lean_object* v_new_587_, lean_object* v_x_588_){
_start:
{
lean_inc_ref(v_new_587_);
return v_new_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object* v_x_589_, lean_object* v_new_590_, lean_object* v_x_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Elab_Tactic_Do_addMData___lam__0(v_x_589_, v_new_590_, v_x_591_);
lean_dec_ref(v_x_591_);
lean_dec_ref(v_new_590_);
lean_dec(v_x_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object* v_d_594_, lean_object* v_e_595_){
_start:
{
if (lean_obj_tag(v_e_595_) == 10)
{
lean_object* v_data_596_; lean_object* v_expr_597_; lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_data_596_ = lean_ctor_get(v_e_595_, 0);
lean_inc(v_data_596_);
v_expr_597_ = lean_ctor_get(v_e_595_, 1);
lean_inc_ref(v_expr_597_);
lean_dec_ref_known(v_e_595_, 2);
v___f_598_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_addMData___closed__0));
v___x_599_ = l_Lean_KVMap_mergeBy(v___f_598_, v_d_594_, v_data_596_);
lean_dec(v_data_596_);
v___x_600_ = l_Lean_Expr_mdata___override(v___x_599_, v_expr_597_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Expr_mdata___override(v_d_594_, v_e_595_);
return v___x_601_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object* v_e_602_){
_start:
{
uint8_t v___y_604_; 
switch(lean_obj_tag(v_e_602_))
{
case 1:
{
uint8_t v___x_606_; 
v___x_606_ = 0;
return v___x_606_;
}
case 5:
{
uint8_t v___x_607_; 
v___x_607_ = l_Lean_Meta_Simp_isOfNatNatLit(v_e_602_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; 
v___x_608_ = l_Lean_Meta_Simp_isOfScientificLit(v_e_602_);
v___y_604_ = v___x_608_;
goto v___jp_603_;
}
else
{
v___y_604_ = v___x_607_;
goto v___jp_603_;
}
}
case 6:
{
uint8_t v___x_609_; 
v___x_609_ = 0;
return v___x_609_;
}
case 7:
{
uint8_t v___x_610_; 
v___x_610_ = 0;
return v___x_610_;
}
case 8:
{
uint8_t v___x_611_; 
v___x_611_ = 0;
return v___x_611_;
}
case 10:
{
lean_object* v_expr_612_; 
v_expr_612_ = lean_ctor_get(v_e_602_, 1);
v_e_602_ = v_expr_612_;
goto _start;
}
case 11:
{
lean_object* v_struct_614_; 
v_struct_614_ = lean_ctor_get(v_e_602_, 2);
v_e_602_ = v_struct_614_;
goto _start;
}
default: 
{
uint8_t v___x_616_; 
v___x_616_ = 1;
return v___x_616_;
}
}
v___jp_603_:
{
if (v___y_604_ == 0)
{
uint8_t v___x_605_; 
v___x_605_ = l_Lean_Meta_Simp_isCharLit(v_e_602_);
return v___x_605_;
}
else
{
return v___y_604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object* v_e_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_e_617_);
lean_dec_ref(v_e_617_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object* v_val_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v_val_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object* v_msgData_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; lean_object* v_env_629_; lean_object* v___x_630_; lean_object* v_toCold_631_; lean_object* v_mctx_632_; lean_object* v_lctx_633_; lean_object* v_options_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_628_ = lean_st_ref_get(v___y_626_);
v_env_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc_ref(v_env_629_);
lean_dec(v___x_628_);
v___x_630_ = lean_st_ref_get(v___y_624_);
v_toCold_631_ = lean_ctor_get(v___y_625_, 0);
v_mctx_632_ = lean_ctor_get(v___x_630_, 0);
lean_inc_ref(v_mctx_632_);
lean_dec(v___x_630_);
v_lctx_633_ = lean_ctor_get(v___y_623_, 2);
v_options_634_ = lean_ctor_get(v_toCold_631_, 2);
lean_inc_ref(v_options_634_);
lean_inc_ref(v_lctx_633_);
v___x_635_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_635_, 0, v_env_629_);
lean_ctor_set(v___x_635_, 1, v_mctx_632_);
lean_ctor_set(v___x_635_, 2, v_lctx_633_);
lean_ctor_set(v___x_635_, 3, v_options_634_);
v___x_636_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v_msgData_622_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object* v_msgData_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object* v_msg_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_ref_651_; lean_object* v___x_652_; lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v_ref_651_ = lean_ctor_get(v___y_648_, 2);
v___x_652_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msg_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_661_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
lean_inc(v_ref_651_);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v_ref_651_);
lean_ctor_set(v___x_657_, 1, v_a_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 1);
lean_ctor_set(v___x_655_, 0, v___x_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object* v_msg_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object* v_data_669_, lean_object* v_expr_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Expr_mdata___override(v_data_669_, v_expr_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object* v_typeName_672_, lean_object* v_idx_673_, lean_object* v_struct_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Expr_proj___override(v_typeName_672_, v_idx_673_, v_struct_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object* v_a_676_, lean_object* v_b_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_678_) == 0)
{
lean_dec(v_b_677_);
lean_dec(v_a_676_);
return v_x_678_;
}
else
{
lean_object* v_key_679_; lean_object* v_value_680_; lean_object* v_tail_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_693_; 
v_key_679_ = lean_ctor_get(v_x_678_, 0);
v_value_680_ = lean_ctor_get(v_x_678_, 1);
v_tail_681_ = lean_ctor_get(v_x_678_, 2);
v_isSharedCheck_693_ = !lean_is_exclusive(v_x_678_);
if (v_isSharedCheck_693_ == 0)
{
v___x_683_ = v_x_678_;
v_isShared_684_ = v_isSharedCheck_693_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_tail_681_);
lean_inc(v_value_680_);
lean_inc(v_key_679_);
lean_dec(v_x_678_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_693_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
uint8_t v___x_685_; 
v___x_685_ = l_Lean_instBEqFVarId_beq(v_key_679_, v_a_676_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_676_, v_b_677_, v_tail_681_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 2, v___x_686_);
v___x_688_ = v___x_683_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_key_679_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_value_680_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
else
{
lean_object* v___x_691_; 
lean_dec(v_value_680_);
lean_dec(v_key_679_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v_b_677_);
lean_ctor_set(v___x_683_, 0, v_a_676_);
v___x_691_ = v___x_683_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_676_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_b_677_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_tail_681_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object* v_m_694_, lean_object* v_a_695_, lean_object* v_b_696_){
_start:
{
lean_object* v_size_697_; lean_object* v_buckets_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_741_; 
v_size_697_ = lean_ctor_get(v_m_694_, 0);
v_buckets_698_ = lean_ctor_get(v_m_694_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_m_694_);
if (v_isSharedCheck_741_ == 0)
{
v___x_700_ = v_m_694_;
v_isShared_701_ = v_isSharedCheck_741_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_buckets_698_);
lean_inc(v_size_697_);
lean_dec(v_m_694_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_741_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v___x_705_; uint64_t v_fold_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; size_t v___x_713_; size_t v___x_714_; lean_object* v_bkt_715_; uint8_t v___x_716_; 
v___x_702_ = lean_array_get_size(v_buckets_698_);
v___x_703_ = l_Lean_instHashableFVarId_hash(v_a_695_);
v___x_704_ = 32ULL;
v___x_705_ = lean_uint64_shift_right(v___x_703_, v___x_704_);
v_fold_706_ = lean_uint64_xor(v___x_703_, v___x_705_);
v___x_707_ = 16ULL;
v___x_708_ = lean_uint64_shift_right(v_fold_706_, v___x_707_);
v___x_709_ = lean_uint64_xor(v_fold_706_, v___x_708_);
v___x_710_ = lean_uint64_to_usize(v___x_709_);
v___x_711_ = lean_usize_of_nat(v___x_702_);
v___x_712_ = ((size_t)1ULL);
v___x_713_ = lean_usize_sub(v___x_711_, v___x_712_);
v___x_714_ = lean_usize_land(v___x_710_, v___x_713_);
v_bkt_715_ = lean_array_uget_borrowed(v_buckets_698_, v___x_714_);
v___x_716_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_695_, v_bkt_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v_size_x27_718_; lean_object* v___x_719_; lean_object* v_buckets_x27_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v_size_x27_718_ = lean_nat_add(v_size_697_, v___x_717_);
lean_dec(v_size_697_);
lean_inc(v_bkt_715_);
v___x_719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_719_, 0, v_a_695_);
lean_ctor_set(v___x_719_, 1, v_b_696_);
lean_ctor_set(v___x_719_, 2, v_bkt_715_);
v_buckets_x27_720_ = lean_array_uset(v_buckets_698_, v___x_714_, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(4u);
v___x_722_ = lean_nat_mul(v_size_x27_718_, v___x_721_);
v___x_723_ = lean_unsigned_to_nat(3u);
v___x_724_ = lean_nat_div(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_array_get_size(v_buckets_x27_720_);
v___x_726_ = lean_nat_dec_le(v___x_724_, v___x_725_);
lean_dec(v___x_724_);
if (v___x_726_ == 0)
{
lean_object* v_val_727_; lean_object* v___x_729_; 
v_val_727_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_720_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v_val_727_);
lean_ctor_set(v___x_700_, 0, v_size_x27_718_);
v___x_729_ = v___x_700_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_size_x27_718_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_val_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
else
{
lean_object* v___x_732_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v_buckets_x27_720_);
lean_ctor_set(v___x_700_, 0, v_size_x27_718_);
v___x_732_ = v___x_700_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_size_x27_718_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_buckets_x27_720_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
lean_object* v___x_734_; lean_object* v_buckets_x27_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
lean_inc(v_bkt_715_);
v___x_734_ = lean_box(0);
v_buckets_x27_735_ = lean_array_uset(v_buckets_698_, v___x_714_, v___x_734_);
v___x_736_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_695_, v_b_696_, v_bkt_715_);
v___x_737_ = lean_array_uset(v_buckets_x27_735_, v___x_714_, v___x_736_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_737_);
v___x_739_ = v___x_700_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_size_697_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v_ngen_745_; lean_object* v_namePrefix_746_; lean_object* v_idx_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_776_; 
v___x_744_ = lean_st_ref_get(v___y_742_);
v_ngen_745_ = lean_ctor_get(v___x_744_, 2);
lean_inc_ref(v_ngen_745_);
lean_dec(v___x_744_);
v_namePrefix_746_ = lean_ctor_get(v_ngen_745_, 0);
v_idx_747_ = lean_ctor_get(v_ngen_745_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_ngen_745_);
if (v_isSharedCheck_776_ == 0)
{
v___x_749_ = v_ngen_745_;
v_isShared_750_ = v_isSharedCheck_776_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_idx_747_);
lean_inc(v_namePrefix_746_);
lean_dec(v_ngen_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_776_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v_env_752_; lean_object* v_nextMacroScope_753_; lean_object* v_auxDeclNGen_754_; lean_object* v_traceState_755_; lean_object* v_cache_756_; lean_object* v_messages_757_; lean_object* v_infoState_758_; lean_object* v_snapshotTasks_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_774_; 
v___x_751_ = lean_st_ref_take(v___y_742_);
v_env_752_ = lean_ctor_get(v___x_751_, 0);
v_nextMacroScope_753_ = lean_ctor_get(v___x_751_, 1);
v_auxDeclNGen_754_ = lean_ctor_get(v___x_751_, 3);
v_traceState_755_ = lean_ctor_get(v___x_751_, 4);
v_cache_756_ = lean_ctor_get(v___x_751_, 5);
v_messages_757_ = lean_ctor_get(v___x_751_, 6);
v_infoState_758_ = lean_ctor_get(v___x_751_, 7);
v_snapshotTasks_759_ = lean_ctor_get(v___x_751_, 8);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v___x_751_, 2);
lean_dec(v_unused_775_);
v___x_761_ = v___x_751_;
v_isShared_762_ = v_isSharedCheck_774_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_snapshotTasks_759_);
lean_inc(v_infoState_758_);
lean_inc(v_messages_757_);
lean_inc(v_cache_756_);
lean_inc(v_traceState_755_);
lean_inc(v_auxDeclNGen_754_);
lean_inc(v_nextMacroScope_753_);
lean_inc(v_env_752_);
lean_dec(v___x_751_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_774_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_r_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
lean_inc(v_idx_747_);
lean_inc(v_namePrefix_746_);
v_r_763_ = l_Lean_Name_num___override(v_namePrefix_746_, v_idx_747_);
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_nat_add(v_idx_747_, v___x_764_);
lean_dec(v_idx_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v___x_765_);
v___x_767_ = v___x_749_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_namePrefix_746_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_765_);
v___x_767_ = v_reuseFailAlloc_773_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 2, v___x_767_);
v___x_769_ = v___x_761_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_env_752_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_nextMacroScope_753_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_auxDeclNGen_754_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_traceState_755_);
lean_ctor_set(v_reuseFailAlloc_772_, 5, v_cache_756_);
lean_ctor_set(v_reuseFailAlloc_772_, 6, v_messages_757_);
lean_ctor_set(v_reuseFailAlloc_772_, 7, v_infoState_758_);
lean_ctor_set(v_reuseFailAlloc_772_, 8, v_snapshotTasks_759_);
v___x_769_ = v_reuseFailAlloc_772_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_st_ref_put(v___y_742_, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v_r_763_);
return v___x_771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_777_);
lean_dec(v___y_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v___x_785_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_783_);
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object* v_a_800_, lean_object* v_x_801_){
_start:
{
if (lean_obj_tag(v_x_801_) == 0)
{
return v_x_801_;
}
else
{
lean_object* v_key_802_; lean_object* v_value_803_; lean_object* v_tail_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_813_; 
v_key_802_ = lean_ctor_get(v_x_801_, 0);
v_value_803_ = lean_ctor_get(v_x_801_, 1);
v_tail_804_ = lean_ctor_get(v_x_801_, 2);
v_isSharedCheck_813_ = !lean_is_exclusive(v_x_801_);
if (v_isSharedCheck_813_ == 0)
{
v___x_806_ = v_x_801_;
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_tail_804_);
lean_inc(v_value_803_);
lean_inc(v_key_802_);
lean_dec(v_x_801_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
uint8_t v___x_808_; 
v___x_808_ = l_Lean_instBEqFVarId_beq(v_key_802_, v_a_800_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_800_, v_tail_804_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 2, v___x_809_);
v___x_811_ = v___x_806_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_key_802_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_value_803_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_del_object(v___x_806_);
lean_dec(v_value_803_);
lean_dec(v_key_802_);
return v_tail_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object* v_a_814_, lean_object* v_x_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_814_, v_x_815_);
lean_dec(v_a_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object* v_m_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_size_819_; lean_object* v_buckets_820_; lean_object* v___x_821_; uint64_t v___x_822_; uint64_t v___x_823_; uint64_t v___x_824_; uint64_t v_fold_825_; uint64_t v___x_826_; uint64_t v___x_827_; uint64_t v___x_828_; size_t v___x_829_; size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; lean_object* v_bkt_834_; uint8_t v___x_835_; 
v_size_819_ = lean_ctor_get(v_m_817_, 0);
v_buckets_820_ = lean_ctor_get(v_m_817_, 1);
v___x_821_ = lean_array_get_size(v_buckets_820_);
v___x_822_ = l_Lean_instHashableFVarId_hash(v_a_818_);
v___x_823_ = 32ULL;
v___x_824_ = lean_uint64_shift_right(v___x_822_, v___x_823_);
v_fold_825_ = lean_uint64_xor(v___x_822_, v___x_824_);
v___x_826_ = 16ULL;
v___x_827_ = lean_uint64_shift_right(v_fold_825_, v___x_826_);
v___x_828_ = lean_uint64_xor(v_fold_825_, v___x_827_);
v___x_829_ = lean_uint64_to_usize(v___x_828_);
v___x_830_ = lean_usize_of_nat(v___x_821_);
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_sub(v___x_830_, v___x_831_);
v___x_833_ = lean_usize_land(v___x_829_, v___x_832_);
v_bkt_834_ = lean_array_uget_borrowed(v_buckets_820_, v___x_833_);
v___x_835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_818_, v_bkt_834_);
if (v___x_835_ == 0)
{
return v_m_817_;
}
else
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_848_; 
lean_inc(v_bkt_834_);
lean_inc_ref(v_buckets_820_);
lean_inc(v_size_819_);
v_isSharedCheck_848_ = !lean_is_exclusive(v_m_817_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; lean_object* v_unused_850_; 
v_unused_849_ = lean_ctor_get(v_m_817_, 1);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_m_817_, 0);
lean_dec(v_unused_850_);
v___x_837_ = v_m_817_;
v_isShared_838_ = v_isSharedCheck_848_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_m_817_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_848_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v_buckets_x27_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_839_ = lean_box(0);
v_buckets_x27_840_ = lean_array_uset(v_buckets_820_, v___x_833_, v___x_839_);
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_sub(v_size_819_, v___x_841_);
lean_dec(v_size_819_);
v___x_843_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_818_, v_bkt_834_);
v___x_844_ = lean_array_uset(v_buckets_x27_840_, v___x_833_, v___x_843_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_844_);
lean_ctor_set(v___x_837_, 0, v___x_842_);
v___x_846_ = v___x_837_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object* v_m_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_851_, v_a_852_);
lean_dec(v_a_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object* v_a_854_, lean_object* v_fallback_855_, lean_object* v_x_856_){
_start:
{
if (lean_obj_tag(v_x_856_) == 0)
{
lean_inc(v_fallback_855_);
return v_fallback_855_;
}
else
{
lean_object* v_key_857_; lean_object* v_value_858_; lean_object* v_tail_859_; uint8_t v___x_860_; 
v_key_857_ = lean_ctor_get(v_x_856_, 0);
v_value_858_ = lean_ctor_get(v_x_856_, 1);
v_tail_859_ = lean_ctor_get(v_x_856_, 2);
v___x_860_ = l_Lean_instBEqFVarId_beq(v_key_857_, v_a_854_);
if (v___x_860_ == 0)
{
v_x_856_ = v_tail_859_;
goto _start;
}
else
{
lean_inc(v_value_858_);
return v_value_858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_862_, lean_object* v_fallback_863_, lean_object* v_x_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_862_, v_fallback_863_, v_x_864_);
lean_dec(v_x_864_);
lean_dec(v_fallback_863_);
lean_dec(v_a_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object* v_m_866_, lean_object* v_a_867_, lean_object* v_fallback_868_){
_start:
{
lean_object* v_buckets_869_; lean_object* v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; uint64_t v___x_873_; uint64_t v_fold_874_; uint64_t v___x_875_; uint64_t v___x_876_; uint64_t v___x_877_; size_t v___x_878_; size_t v___x_879_; size_t v___x_880_; size_t v___x_881_; size_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_buckets_869_ = lean_ctor_get(v_m_866_, 1);
v___x_870_ = lean_array_get_size(v_buckets_869_);
v___x_871_ = l_Lean_instHashableFVarId_hash(v_a_867_);
v___x_872_ = 32ULL;
v___x_873_ = lean_uint64_shift_right(v___x_871_, v___x_872_);
v_fold_874_ = lean_uint64_xor(v___x_871_, v___x_873_);
v___x_875_ = 16ULL;
v___x_876_ = lean_uint64_shift_right(v_fold_874_, v___x_875_);
v___x_877_ = lean_uint64_xor(v_fold_874_, v___x_876_);
v___x_878_ = lean_uint64_to_usize(v___x_877_);
v___x_879_ = lean_usize_of_nat(v___x_870_);
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_sub(v___x_879_, v___x_880_);
v___x_882_ = lean_usize_land(v___x_878_, v___x_881_);
v___x_883_ = lean_array_uget_borrowed(v_buckets_869_, v___x_882_);
v___x_884_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_867_, v_fallback_868_, v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object* v_m_885_, lean_object* v_a_886_, lean_object* v_fallback_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_885_, v_a_886_, v_fallback_887_);
lean_dec(v_fallback_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_m_885_);
return v_res_888_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_box(0);
v___x_893_ = lean_unsigned_to_nat(16u);
v___x_894_ = lean_mk_array(v___x_893_, v___x_892_);
return v___x_894_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__1(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__0));
v___x_901_ = l_Lean_stringToMessageData(v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__3(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__2));
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__5(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__4));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object* v_e_908_, lean_object* v_subst_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
switch(lean_obj_tag(v_e_908_))
{
case 0:
{
lean_object* v_deBruijnIndex_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_deBruijnIndex_915_ = lean_ctor_get(v_e_908_, 0);
v___x_916_ = lean_array_get_size(v_subst_909_);
v___x_917_ = lean_nat_dec_lt(v_deBruijnIndex_915_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_inc(v_deBruijnIndex_915_);
lean_dec_ref_known(v_e_908_, 1);
lean_dec_ref(v_subst_909_);
v___x_918_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__1, &l_Lean_Elab_Tactic_Do_countUses___closed__1_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__1);
v___x_919_ = l_Nat_reprFast(v_deBruijnIndex_915_);
v___x_920_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
v___x_921_ = l_Lean_MessageData_ofFormat(v___x_920_);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_918_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__3, &l_Lean_Elab_Tactic_Do_countUses___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__3);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Nat_reprFast(v___x_916_);
v___x_926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
v___x_927_ = l_Lean_MessageData_ofFormat(v___x_926_);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_924_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_928_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
return v___x_929_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = lean_nat_sub(v___x_916_, v___x_930_);
v___x_932_ = lean_nat_sub(v___x_931_, v_deBruijnIndex_915_);
lean_dec(v___x_931_);
v___x_933_ = lean_array_fget(v_subst_909_, v___x_932_);
lean_dec(v___x_932_);
lean_dec_ref(v_subst_909_);
v___x_934_ = 1;
v___x_935_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_936_ = lean_box(v___x_934_);
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_935_, v___x_933_, v___x_936_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_e_908_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
case 1:
{
lean_object* v_fvarId_940_; uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec_ref(v_subst_909_);
v_fvarId_940_ = lean_ctor_get(v_e_908_, 0);
v___x_941_ = 1;
v___x_942_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_943_ = lean_box(v___x_941_);
lean_inc(v_fvarId_940_);
v___x_944_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_942_, v_fvarId_940_, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_e_908_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
case 5:
{
lean_object* v_fn_947_; lean_object* v_arg_948_; lean_object* v___x_949_; 
v_fn_947_ = lean_ctor_get(v_e_908_, 0);
lean_inc_ref(v_fn_947_);
v_arg_948_ = lean_ctor_get(v_e_908_, 1);
lean_inc_ref(v_arg_948_);
lean_dec_ref_known(v_e_908_, 2);
lean_inc_ref(v_subst_909_);
v___x_949_ = l_Lean_Elab_Tactic_Do_countUses(v_fn_947_, v_subst_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v_fst_951_; lean_object* v_snd_952_; lean_object* v___x_953_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v_fst_951_ = lean_ctor_get(v_a_950_, 0);
lean_inc(v_fst_951_);
v_snd_952_ = lean_ctor_get(v_a_950_, 1);
lean_inc(v_snd_952_);
lean_dec(v_a_950_);
v___x_953_ = l_Lean_Elab_Tactic_Do_countUses(v_arg_948_, v_subst_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_972_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_972_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_972_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_972_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_fst_958_; lean_object* v_snd_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_971_; 
v_fst_958_ = lean_ctor_get(v_a_954_, 0);
v_snd_959_ = lean_ctor_get(v_a_954_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v_a_954_);
if (v_isSharedCheck_971_ == 0)
{
v___x_961_ = v_a_954_;
v_isShared_962_ = v_isSharedCheck_971_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_snd_959_);
lean_inc(v_fst_958_);
lean_dec(v_a_954_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_971_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_963_ = l_Lean_Expr_app___override(v_fst_951_, v_fst_958_);
v___x_964_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_952_, v_snd_959_);
lean_dec(v_snd_952_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_964_);
lean_ctor_set(v___x_961_, 0, v___x_963_);
v___x_966_ = v___x_961_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_966_);
v___x_968_ = v___x_956_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
else
{
lean_dec(v_snd_952_);
lean_dec(v_fst_951_);
return v___x_953_;
}
}
else
{
lean_dec_ref(v_arg_948_);
lean_dec_ref(v_subst_909_);
return v___x_949_;
}
}
case 6:
{
lean_object* v_binderName_973_; lean_object* v_binderType_974_; lean_object* v_body_975_; uint8_t v_binderInfo_976_; lean_object* v___x_977_; 
v_binderName_973_ = lean_ctor_get(v_e_908_, 0);
lean_inc(v_binderName_973_);
v_binderType_974_ = lean_ctor_get(v_e_908_, 1);
lean_inc_ref(v_binderType_974_);
v_body_975_ = lean_ctor_get(v_e_908_, 2);
lean_inc_ref(v_body_975_);
v_binderInfo_976_ = lean_ctor_get_uint8(v_e_908_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_908_, 3);
v___x_977_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
lean_inc_ref(v_subst_909_);
v___x_979_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_974_, v_subst_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v_fst_981_; lean_object* v_snd_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v_fst_981_ = lean_ctor_get(v_a_980_, 0);
lean_inc(v_fst_981_);
v_snd_982_ = lean_ctor_get(v_a_980_, 1);
lean_inc(v_snd_982_);
lean_dec(v_a_980_);
lean_inc(v_a_978_);
v___x_983_ = lean_array_push(v_subst_909_, v_a_978_);
v___x_984_ = l_Lean_Elab_Tactic_Do_countUses(v_body_975_, v___x_983_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1004_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_1004_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1004_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_fst_989_; lean_object* v_snd_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1003_; 
v_fst_989_ = lean_ctor_get(v_a_985_, 0);
v_snd_990_ = lean_ctor_get(v_a_985_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_a_985_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_992_ = v_a_985_;
v_isShared_993_ = v_isSharedCheck_1003_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_snd_990_);
lean_inc(v_fst_989_);
lean_dec(v_a_985_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1003_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_994_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_982_, v_snd_990_);
lean_dec(v_snd_982_);
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_994_, v_a_978_);
lean_dec(v_a_978_);
v___x_996_ = l_Lean_Expr_lam___override(v_binderName_973_, v_fst_981_, v_fst_989_, v_binderInfo_976_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v___x_995_);
lean_ctor_set(v___x_992_, 0, v___x_996_);
v___x_998_ = v___x_992_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_995_);
v___x_998_ = v_reuseFailAlloc_1002_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_1000_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_998_);
v___x_1000_ = v___x_987_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
else
{
lean_dec(v_snd_982_);
lean_dec(v_fst_981_);
lean_dec(v_a_978_);
lean_dec(v_binderName_973_);
return v___x_984_;
}
}
else
{
lean_dec(v_a_978_);
lean_dec_ref(v_body_975_);
lean_dec(v_binderName_973_);
lean_dec_ref(v_subst_909_);
return v___x_979_;
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec_ref(v_body_975_);
lean_dec_ref(v_binderType_974_);
lean_dec(v_binderName_973_);
lean_dec_ref(v_subst_909_);
v_a_1005_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_977_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_977_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1013_; lean_object* v_binderType_1014_; lean_object* v_body_1015_; uint8_t v_binderInfo_1016_; lean_object* v___x_1017_; 
v_binderName_1013_ = lean_ctor_get(v_e_908_, 0);
lean_inc(v_binderName_1013_);
v_binderType_1014_ = lean_ctor_get(v_e_908_, 1);
lean_inc_ref(v_binderType_1014_);
v_body_1015_ = lean_ctor_get(v_e_908_, 2);
lean_inc_ref(v_body_1015_);
v_binderInfo_1016_ = lean_ctor_get_uint8(v_e_908_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_908_, 3);
v___x_1017_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
lean_inc_ref(v_subst_909_);
v___x_1019_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1014_, v_subst_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v_fst_1021_; lean_object* v_snd_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v_fst_1021_ = lean_ctor_get(v_a_1020_, 0);
lean_inc(v_fst_1021_);
v_snd_1022_ = lean_ctor_get(v_a_1020_, 1);
lean_inc(v_snd_1022_);
lean_dec(v_a_1020_);
lean_inc(v_a_1018_);
v___x_1023_ = lean_array_push(v_subst_909_, v_a_1018_);
v___x_1024_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1015_, v___x_1023_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1044_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1044_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1044_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_fst_1029_; lean_object* v_snd_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1043_; 
v_fst_1029_ = lean_ctor_get(v_a_1025_, 0);
v_snd_1030_ = lean_ctor_get(v_a_1025_, 1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_a_1025_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1032_ = v_a_1025_;
v_isShared_1033_ = v_isSharedCheck_1043_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_snd_1030_);
lean_inc(v_fst_1029_);
lean_dec(v_a_1025_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1043_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1034_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_1022_, v_snd_1030_);
lean_dec(v_snd_1022_);
v___x_1035_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1034_, v_a_1018_);
lean_dec(v_a_1018_);
v___x_1036_ = l_Lean_Expr_forallE___override(v_binderName_1013_, v_fst_1021_, v_fst_1029_, v_binderInfo_1016_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v___x_1035_);
lean_ctor_set(v___x_1032_, 0, v___x_1036_);
v___x_1038_ = v___x_1032_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1035_);
v___x_1038_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1040_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1038_);
v___x_1040_ = v___x_1027_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
else
{
lean_dec(v_snd_1022_);
lean_dec(v_fst_1021_);
lean_dec(v_a_1018_);
lean_dec(v_binderName_1013_);
return v___x_1024_;
}
}
else
{
lean_dec(v_a_1018_);
lean_dec_ref(v_body_1015_);
lean_dec(v_binderName_1013_);
lean_dec_ref(v_subst_909_);
return v___x_1019_;
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v_body_1015_);
lean_dec_ref(v_binderType_1014_);
lean_dec(v_binderName_1013_);
lean_dec_ref(v_subst_909_);
v_a_1045_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1017_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1017_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
case 8:
{
lean_object* v_declName_1053_; lean_object* v_type_1054_; lean_object* v_value_1055_; lean_object* v_body_1056_; uint8_t v_nondep_1057_; lean_object* v___x_1058_; 
v_declName_1053_ = lean_ctor_get(v_e_908_, 0);
lean_inc(v_declName_1053_);
v_type_1054_ = lean_ctor_get(v_e_908_, 1);
lean_inc_ref(v_type_1054_);
v_value_1055_ = lean_ctor_get(v_e_908_, 2);
lean_inc_ref(v_value_1055_);
v_body_1056_ = lean_ctor_get(v_e_908_, 3);
lean_inc_ref(v_body_1056_);
v_nondep_1057_ = lean_ctor_get_uint8(v_e_908_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_908_, 4);
v___x_1058_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc_n(v_a_1059_, 2);
lean_dec_ref_known(v___x_1058_, 1);
lean_inc_ref(v_subst_909_);
v___x_1060_ = lean_array_push(v_subst_909_, v_a_1059_);
v___x_1061_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1056_, v___x_1060_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1104_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1104_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1104_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_fst_1066_; lean_object* v_snd_1067_; lean_object* v___x_1069_; 
v_fst_1066_ = lean_ctor_get(v_a_1062_, 0);
lean_inc(v_fst_1066_);
v_snd_1067_ = lean_ctor_get(v_a_1062_, 1);
lean_inc(v_snd_1067_);
lean_dec(v_a_1062_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 1);
lean_ctor_set(v___x_1064_, 0, v_value_1055_);
v___x_1069_ = v___x_1064_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_value_1055_);
v___x_1069_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_a_1059_, v_type_1054_, v___x_1069_, v_snd_1067_, v_subst_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_1059_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1094_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1094_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1094_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v_snd_1075_; lean_object* v_fst_1076_; 
v_snd_1075_ = lean_ctor_get(v_a_1071_, 1);
lean_inc(v_snd_1075_);
v_fst_1076_ = lean_ctor_get(v_snd_1075_, 0);
lean_inc(v_fst_1076_);
if (lean_obj_tag(v_fst_1076_) == 1)
{
lean_object* v_fst_1077_; lean_object* v_snd_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1090_; 
v_fst_1077_ = lean_ctor_get(v_a_1071_, 0);
lean_inc(v_fst_1077_);
lean_dec(v_a_1071_);
v_snd_1078_ = lean_ctor_get(v_snd_1075_, 1);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_snd_1075_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_snd_1075_, 0);
lean_dec(v_unused_1091_);
v___x_1080_ = v_snd_1075_;
v_isShared_1081_ = v_isSharedCheck_1090_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_snd_1078_);
lean_dec(v_snd_1075_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1090_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v_val_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v_val_1082_ = lean_ctor_get(v_fst_1076_, 0);
lean_inc(v_val_1082_);
lean_dec_ref_known(v_fst_1076_, 1);
v___x_1083_ = l_Lean_Expr_letE___override(v_declName_1053_, v_fst_1077_, v_val_1082_, v_fst_1066_, v_nondep_1057_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1083_);
v___x_1085_ = v___x_1080_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_snd_1078_);
v___x_1085_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1087_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1085_);
v___x_1087_ = v___x_1073_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec(v_fst_1076_);
lean_dec(v_snd_1075_);
lean_del_object(v___x_1073_);
lean_dec(v_a_1071_);
lean_dec(v_fst_1066_);
lean_dec(v_declName_1053_);
v___x_1092_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
v___x_1093_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_1092_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
return v___x_1093_;
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec(v_fst_1066_);
lean_dec(v_declName_1053_);
v_a_1095_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1070_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1070_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1059_);
lean_dec_ref(v_value_1055_);
lean_dec_ref(v_type_1054_);
lean_dec(v_declName_1053_);
lean_dec_ref(v_subst_909_);
return v___x_1061_;
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v_body_1056_);
lean_dec_ref(v_value_1055_);
lean_dec_ref(v_type_1054_);
lean_dec(v_declName_1053_);
lean_dec_ref(v_subst_909_);
v_a_1105_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1058_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1058_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
case 10:
{
lean_object* v_data_1113_; lean_object* v_expr_1114_; lean_object* v___x_1115_; 
v_data_1113_ = lean_ctor_get(v_e_908_, 0);
lean_inc(v_data_1113_);
v_expr_1114_ = lean_ctor_get(v_e_908_, 1);
lean_inc_ref(v_expr_1114_);
lean_dec_ref_known(v_e_908_, 2);
v___x_1115_ = l_Lean_Elab_Tactic_Do_countUses(v_expr_1114_, v_subst_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1125_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__0), 2, 1);
lean_closure_set(v___f_1120_, 0, v_data_1113_);
v___x_1121_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1120_, v_a_1116_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1121_);
v___x_1123_ = v___x_1118_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_dec(v_data_1113_);
return v___x_1115_;
}
}
case 11:
{
lean_object* v_typeName_1126_; lean_object* v_idx_1127_; lean_object* v_struct_1128_; lean_object* v___x_1129_; 
v_typeName_1126_ = lean_ctor_get(v_e_908_, 0);
lean_inc(v_typeName_1126_);
v_idx_1127_ = lean_ctor_get(v_e_908_, 1);
lean_inc(v_idx_1127_);
v_struct_1128_ = lean_ctor_get(v_e_908_, 2);
lean_inc_ref(v_struct_1128_);
lean_dec_ref_known(v_e_908_, 3);
v___x_1129_ = l_Lean_Elab_Tactic_Do_countUses(v_struct_1128_, v_subst_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1139_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1139_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1139_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___f_1134_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__1), 3, 2);
lean_closure_set(v___f_1134_, 0, v_typeName_1126_);
lean_closure_set(v___f_1134_, 1, v_idx_1127_);
v___x_1135_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1134_, v_a_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1135_);
v___x_1137_ = v___x_1132_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
else
{
lean_dec(v_idx_1127_);
lean_dec(v_typeName_1126_);
return v___x_1129_;
}
}
default: 
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v_subst_909_);
v___x_1140_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_e_908_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object* v_fvarId_1143_, lean_object* v_ty_1144_, lean_object* v_val_x3f_1145_, lean_object* v_bodyUses_1146_, lean_object* v_subst_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1153_; 
lean_inc_ref(v_subst_1147_);
v___x_1153_ = l_Lean_Elab_Tactic_Do_countUses(v_ty_1144_, v_subst_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1209_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1209_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1209_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_fst_1158_; lean_object* v_snd_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1208_; 
v_fst_1158_ = lean_ctor_get(v_a_1154_, 0);
v_snd_1159_ = lean_ctor_get(v_a_1154_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_a_1154_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1161_ = v_a_1154_;
v_isShared_1162_ = v_isSharedCheck_1208_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_snd_1159_);
lean_inc(v_fst_1158_);
lean_dec(v_a_1154_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1208_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___y_1164_; uint8_t v___y_1165_; lean_object* v___y_1166_; lean_object* v_fst_1181_; lean_object* v_snd_1182_; 
if (lean_obj_tag(v_val_x3f_1145_) == 0)
{
lean_object* v___x_1192_; 
lean_dec_ref(v_subst_1147_);
v___x_1192_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v_fst_1181_ = v_val_x3f_1145_;
v_snd_1182_ = v___x_1192_;
goto v___jp_1180_;
}
else
{
lean_object* v_val_1193_; lean_object* v___x_1194_; 
v_val_1193_ = lean_ctor_get(v_val_x3f_1145_, 0);
lean_inc(v_val_1193_);
lean_dec_ref_known(v_val_x3f_1145_, 1);
v___x_1194_ = l_Lean_Elab_Tactic_Do_countUses(v_val_1193_, v_subst_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___f_1196_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4));
v___x_1197_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1196_, v_a_1195_);
v_fst_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_fst_1198_);
v_snd_1199_ = lean_ctor_get(v___x_1197_, 1);
lean_inc(v_snd_1199_);
lean_dec_ref(v___x_1197_);
v_fst_1181_ = v_fst_1198_;
v_snd_1182_ = v_snd_1199_;
goto v___jp_1180_;
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_del_object(v___x_1161_);
lean_dec(v_snd_1159_);
lean_dec(v_fst_1158_);
lean_del_object(v___x_1156_);
lean_dec_ref(v_bodyUses_1146_);
v_a_1200_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1194_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1194_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
v___jp_1163_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1167_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_1166_, v_fvarId_1143_);
v___x_1168_ = lean_box(0);
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1170_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1165_);
v___x_1171_ = l_Lean_KVMap_setNat(v___x_1168_, v___x_1169_, v___x_1170_);
v___x_1172_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1171_, v_fst_1158_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1167_);
lean_ctor_set(v___x_1161_, 0, v___y_1164_);
v___x_1174_ = v___x_1161_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___y_1164_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1167_);
v___x_1174_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1172_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1175_);
v___x_1177_ = v___x_1156_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
v___jp_1180_:
{
uint8_t v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1183_ = 0;
v___x_1184_ = lean_box(v___x_1183_);
v___x_1185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_1146_, v_fvarId_1143_, v___x_1184_);
lean_dec(v___x_1184_);
v___x_1186_ = lean_unbox(v___x_1185_);
v___x_1187_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_1186_, v___x_1183_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1188_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_1146_, v_snd_1159_);
lean_dec_ref(v_bodyUses_1146_);
v___x_1189_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_1188_, v_snd_1182_);
lean_dec_ref(v___x_1188_);
v___x_1190_ = lean_unbox(v___x_1185_);
lean_dec(v___x_1185_);
v___y_1164_ = v_fst_1181_;
v___y_1165_ = v___x_1190_;
v___y_1166_ = v___x_1189_;
goto v___jp_1163_;
}
else
{
uint8_t v___x_1191_; 
lean_dec_ref(v_snd_1182_);
lean_dec(v_snd_1159_);
v___x_1191_ = lean_unbox(v___x_1185_);
lean_dec(v___x_1185_);
v___y_1164_ = v_fst_1181_;
v___y_1165_ = v___x_1191_;
v___y_1166_ = v_bodyUses_1146_;
goto v___jp_1163_;
}
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_subst_1147_);
lean_dec_ref(v_bodyUses_1146_);
lean_dec(v_val_x3f_1145_);
v_a_1210_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1153_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1153_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object* v_fvarId_1218_, lean_object* v_ty_1219_, lean_object* v_val_x3f_1220_, lean_object* v_bodyUses_1221_, lean_object* v_subst_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1218_, v_ty_1219_, v_val_x3f_1220_, v_bodyUses_1221_, v_subst_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_fvarId_1218_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object* v_e_1229_, lean_object* v_subst_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Elab_Tactic_Do_countUses(v_e_1229_, v_subst_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object* v_00_u03b2_1237_, lean_object* v_m_1238_, lean_object* v_a_1239_, lean_object* v_fallback_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_1238_, v_a_1239_, v_fallback_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object* v_00_u03b2_1242_, lean_object* v_m_1243_, lean_object* v_a_1244_, lean_object* v_fallback_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_1242_, v_m_1243_, v_a_1244_, v_fallback_1245_);
lean_dec(v_fallback_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_m_1243_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object* v_00_u03b2_1247_, lean_object* v_m_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_1248_, v_a_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object* v_00_u03b2_1251_, lean_object* v_m_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(v_00_u03b2_1251_, v_m_1252_, v_a_1253_);
lean_dec(v_a_1253_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object* v_00_u03b1_1255_, lean_object* v_msg_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object* v_00_u03b1_1263_, lean_object* v_msg_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(v_00_u03b1_1263_, v_msg_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object* v_00_u03b2_1271_, lean_object* v_m_1272_, lean_object* v_a_1273_, lean_object* v_b_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_1272_, v_a_1273_, v_b_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object* v_00_u03b2_1288_, lean_object* v_a_1289_, lean_object* v_fallback_1290_, lean_object* v_x_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_1289_, v_fallback_1290_, v_x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1293_, lean_object* v_a_1294_, lean_object* v_fallback_1295_, lean_object* v_x_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_1293_, v_a_1294_, v_fallback_1295_, v_x_1296_);
lean_dec(v_x_1296_);
lean_dec(v_fallback_1295_);
lean_dec(v_a_1294_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object* v_00_u03b2_1298_, lean_object* v_a_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_1299_, v_x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1302_, lean_object* v_a_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_1302_, v_a_1303_, v_x_1304_);
lean_dec(v_a_1303_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object* v_00_u03b2_1306_, lean_object* v_a_1307_, lean_object* v_b_1308_, lean_object* v_x_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_1307_, v_b_1308_, v_x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object* v_as_1313_, size_t v_i_1314_, size_t v_stop_1315_, lean_object* v_b_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_usize_dec_eq(v_i_1314_, v_stop_1315_);
if (v___x_1322_ == 0)
{
size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_sub(v_i_1314_, v___x_1323_);
v___x_1325_ = lean_array_uget_borrowed(v_as_1313_, v___x_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
v_i_1314_ = v___x_1324_;
goto _start;
}
else
{
lean_object* v_val_1327_; lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_val_1327_ = lean_ctor_get(v___x_1325_, 0);
v_fst_1328_ = lean_ctor_get(v_b_1316_, 0);
lean_inc(v_fst_1328_);
v_snd_1329_ = lean_ctor_get(v_b_1316_, 1);
lean_inc(v_snd_1329_);
lean_dec_ref(v_b_1316_);
v___x_1330_ = l_Lean_LocalDecl_fvarId(v_val_1327_);
v___x_1331_ = l_Lean_LocalDecl_type(v_val_1327_);
v___x_1332_ = l_Lean_LocalDecl_value_x3f(v_val_1327_, v___x_1322_);
v___x_1333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_1334_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v___x_1330_, v___x_1331_, v___x_1332_, v_snd_1329_, v___x_1333_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___x_1330_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v_snd_1336_; lean_object* v_fst_1337_; lean_object* v_fst_1338_; lean_object* v_snd_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1354_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1334_, 1);
v_snd_1336_ = lean_ctor_get(v_a_1335_, 1);
lean_inc(v_snd_1336_);
v_fst_1337_ = lean_ctor_get(v_a_1335_, 0);
lean_inc(v_fst_1337_);
lean_dec(v_a_1335_);
v_fst_1338_ = lean_ctor_get(v_snd_1336_, 0);
v_snd_1339_ = lean_ctor_get(v_snd_1336_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_snd_1336_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1341_ = v_snd_1336_;
v_isShared_1342_ = v_isSharedCheck_1354_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_snd_1339_);
lean_inc(v_fst_1338_);
lean_dec(v_snd_1336_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1354_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___y_1344_; 
if (lean_obj_tag(v_fst_1338_) == 0)
{
lean_object* v___x_1350_; 
lean_inc(v_val_1327_);
v___x_1350_ = l_Lean_LocalDecl_setType(v_val_1327_, v_fst_1337_);
v___y_1344_ = v___x_1350_;
goto v___jp_1343_;
}
else
{
lean_object* v_val_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_val_1351_ = lean_ctor_get(v_fst_1338_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v_fst_1338_, 1);
lean_inc(v_val_1327_);
v___x_1352_ = l_Lean_LocalDecl_setType(v_val_1327_, v_fst_1337_);
v___x_1353_ = l_Lean_LocalDecl_setValue(v___x_1352_, v_val_1351_);
v___y_1344_ = v___x_1353_;
goto v___jp_1343_;
}
v___jp_1343_:
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1345_ = lean_array_push(v_fst_1328_, v___y_1344_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1345_);
v___x_1347_ = v___x_1341_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_snd_1339_);
v___x_1347_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
v_i_1314_ = v___x_1324_;
v_b_1316_ = v___x_1347_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_fst_1328_);
v_a_1355_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1334_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1334_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
else
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v_b_1316_);
return v___x_1363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1364_, lean_object* v_i_1365_, lean_object* v_stop_1366_, lean_object* v_b_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
size_t v_i_boxed_1373_; size_t v_stop_boxed_1374_; lean_object* v_res_1375_; 
v_i_boxed_1373_ = lean_unbox_usize(v_i_1365_);
lean_dec(v_i_1365_);
v_stop_boxed_1374_ = lean_unbox_usize(v_stop_1366_);
lean_dec(v_stop_1366_);
v_res_1375_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1364_, v_i_boxed_1373_, v_stop_boxed_1374_, v_b_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec_ref(v_as_1364_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object* v_x_1376_, lean_object* v_x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
lean_object* v_cs_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1396_; 
v_cs_1383_ = lean_ctor_get(v_x_1376_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_x_1376_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1385_ = v_x_1376_;
v_isShared_1386_ = v_isSharedCheck_1396_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_cs_1383_);
lean_dec(v_x_1376_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1396_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1387_ = lean_array_get_size(v_cs_1383_);
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = lean_nat_dec_lt(v___x_1388_, v___x_1387_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1391_; 
lean_dec_ref(v_cs_1383_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v_x_1377_);
v___x_1391_ = v___x_1385_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_x_1377_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
else
{
size_t v___x_1393_; size_t v___x_1394_; lean_object* v___x_1395_; 
lean_del_object(v___x_1385_);
v___x_1393_ = lean_usize_of_nat(v___x_1387_);
v___x_1394_ = ((size_t)0ULL);
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_1383_, v___x_1393_, v___x_1394_, v_x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec_ref(v_cs_1383_);
return v___x_1395_;
}
}
}
else
{
lean_object* v_vs_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1410_; 
v_vs_1397_ = lean_ctor_get(v_x_1376_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_x_1376_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1399_ = v_x_1376_;
v_isShared_1400_ = v_isSharedCheck_1410_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_vs_1397_);
lean_dec(v_x_1376_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1410_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1401_ = lean_array_get_size(v_vs_1397_);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_nat_dec_lt(v___x_1402_, v___x_1401_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1405_; 
lean_dec_ref(v_vs_1397_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set_tag(v___x_1399_, 0);
lean_ctor_set(v___x_1399_, 0, v_x_1377_);
v___x_1405_ = v___x_1399_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_x_1377_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
else
{
size_t v___x_1407_; size_t v___x_1408_; lean_object* v___x_1409_; 
lean_del_object(v___x_1399_);
v___x_1407_ = lean_usize_of_nat(v___x_1401_);
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_1397_, v___x_1407_, v___x_1408_, v_x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec_ref(v_vs_1397_);
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_1411_, size_t v_i_1412_, size_t v_stop_1413_, lean_object* v_b_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_usize_dec_eq(v_i_1412_, v_stop_1413_);
if (v___x_1420_ == 0)
{
size_t v___x_1421_; size_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_sub(v_i_1412_, v___x_1421_);
v___x_1423_ = lean_array_uget_borrowed(v_as_1411_, v___x_1422_);
lean_inc(v___x_1423_);
v___x_1424_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_1423_, v_b_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v_i_1412_ = v___x_1422_;
v_b_1414_ = v_a_1425_;
goto _start;
}
else
{
return v___x_1424_;
}
}
else
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_b_1414_);
return v___x_1427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1428_, lean_object* v_i_1429_, lean_object* v_stop_1430_, lean_object* v_b_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
size_t v_i_boxed_1437_; size_t v_stop_boxed_1438_; lean_object* v_res_1439_; 
v_i_boxed_1437_ = lean_unbox_usize(v_i_1429_);
lean_dec(v_i_1429_);
v_stop_boxed_1438_ = lean_unbox_usize(v_stop_1430_);
lean_dec(v_stop_1430_);
v_res_1439_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1428_, v_i_boxed_1437_, v_stop_boxed_1438_, v_b_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_as_1428_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1440_, v_x_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object* v_t_1448_, lean_object* v_init_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_root_1455_; lean_object* v_tail_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_root_1455_ = lean_ctor_get(v_t_1448_, 0);
lean_inc_ref(v_root_1455_);
v_tail_1456_ = lean_ctor_get(v_t_1448_, 1);
lean_inc_ref(v_tail_1456_);
lean_dec_ref(v_t_1448_);
v___x_1457_ = lean_array_get_size(v_tail_1456_);
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = lean_nat_dec_lt(v___x_1458_, v___x_1457_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v_tail_1456_);
v___x_1460_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1455_, v_init_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1460_;
}
else
{
size_t v___x_1461_; size_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = lean_usize_of_nat(v___x_1457_);
v___x_1462_ = ((size_t)0ULL);
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_1456_, v___x_1461_, v___x_1462_, v_init_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec_ref(v_tail_1456_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1455_, v_a_1464_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1465_;
}
else
{
lean_dec_ref(v_root_1455_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object* v_t_1466_, lean_object* v_init_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1466_, v_init_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object* v_lctx_1474_, lean_object* v_init_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_decls_1481_; lean_object* v___x_1482_; 
v_decls_1481_ = lean_ctor_get(v_lctx_1474_, 1);
lean_inc_ref(v_decls_1481_);
lean_dec_ref(v_lctx_1474_);
v___x_1482_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_1481_, v_init_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object* v_lctx_1483_, lean_object* v_init_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1483_, v_init_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t v_sz_1491_, size_t v_i_1492_, lean_object* v_bs_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_usize_dec_lt(v_i_1492_, v_sz_1491_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_bs_1493_);
return v___x_1497_;
}
else
{
lean_object* v_v_1498_; lean_object* v___x_1499_; lean_object* v_bs_x27_1500_; lean_object* v_a_1502_; 
v_v_1498_ = lean_array_uget(v_bs_1493_, v_i_1492_);
v___x_1499_ = lean_unsigned_to_nat(0u);
v_bs_x27_1500_ = lean_array_uset(v_bs_1493_, v_i_1492_, v___x_1499_);
if (lean_obj_tag(v_v_1498_) == 0)
{
v_a_1502_ = v_v_1498_;
goto v___jp_1501_;
}
else
{
lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1521_; 
v_isSharedCheck_1521_ = !lean_is_exclusive(v_v_1498_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; 
v_unused_1522_ = lean_ctor_get(v_v_1498_, 0);
lean_dec(v_unused_1522_);
v___x_1508_ = v_v_1498_;
v_isShared_1509_ = v_isSharedCheck_1521_;
goto v_resetjp_1507_;
}
else
{
lean_dec(v_v_1498_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1521_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1510_ = lean_st_ref_take(v___y_1494_);
v___x_1511_ = l_Lean_instInhabitedLocalDecl_default;
v___x_1512_ = lean_array_get_size(v___x_1510_);
v___x_1513_ = lean_unsigned_to_nat(1u);
v___x_1514_ = lean_nat_sub(v___x_1512_, v___x_1513_);
v___x_1515_ = lean_array_get(v___x_1511_, v___x_1510_, v___x_1514_);
lean_dec(v___x_1514_);
v___x_1516_ = lean_array_pop(v___x_1510_);
v___x_1517_ = lean_st_ref_put(v___y_1494_, v___x_1516_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1515_);
v___x_1519_ = v___x_1508_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1515_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
v_a_1502_ = v___x_1519_;
goto v___jp_1501_;
}
}
}
v___jp_1501_:
{
size_t v___x_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1492_, v___x_1503_);
v___x_1505_ = lean_array_uset(v_bs_x27_1500_, v_i_1492_, v_a_1502_);
v_i_1492_ = v___x_1504_;
v_bs_1493_ = v___x_1505_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object* v_sz_1523_, lean_object* v_i_1524_, lean_object* v_bs_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
size_t v_sz_boxed_1528_; size_t v_i_boxed_1529_; lean_object* v_res_1530_; 
v_sz_boxed_1528_ = lean_unbox_usize(v_sz_1523_);
lean_dec(v_sz_1523_);
v_i_boxed_1529_ = lean_unbox_usize(v_i_1524_);
lean_dec(v_i_1524_);
v_res_1530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_1528_, v_i_boxed_1529_, v_bs_1525_, v___y_1526_);
lean_dec(v___y_1526_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object* v_x_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
if (lean_obj_tag(v_x_1531_) == 0)
{
lean_object* v_cs_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1564_; 
v_cs_1538_ = lean_ctor_get(v_x_1531_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1540_ = v_x_1531_;
v_isShared_1541_ = v_isSharedCheck_1564_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_cs_1538_);
lean_dec(v_x_1531_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1564_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
size_t v_sz_1542_; size_t v___x_1543_; lean_object* v___x_1544_; 
v_sz_1542_ = lean_array_size(v_cs_1538_);
v___x_1543_ = ((size_t)0ULL);
v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1542_, v___x_1543_, v_cs_1538_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1555_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v_a_1545_);
v___x_1550_ = v___x_1540_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1550_);
v___x_1552_ = v___x_1547_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_del_object(v___x_1540_);
v_a_1556_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1544_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1544_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
else
{
lean_object* v_vs_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1591_; 
v_vs_1565_ = lean_ctor_get(v_x_1531_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1567_ = v_x_1531_;
v_isShared_1568_ = v_isSharedCheck_1591_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_vs_1565_);
lean_dec(v_x_1531_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1591_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
size_t v_sz_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
v_sz_1569_ = lean_array_size(v_vs_1565_);
v___x_1570_ = ((size_t)0ULL);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1569_, v___x_1570_, v_vs_1565_, v___y_1532_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1582_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v_a_1572_);
v___x_1577_ = v___x_1567_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1579_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1577_);
v___x_1579_ = v___x_1574_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_del_object(v___x_1567_);
v_a_1583_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1571_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1571_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t v_sz_1592_, size_t v_i_1593_, lean_object* v_bs_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
uint8_t v___x_1601_; 
v___x_1601_ = lean_usize_dec_lt(v_i_1593_, v_sz_1592_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_bs_1594_);
return v___x_1602_;
}
else
{
lean_object* v_v_1603_; lean_object* v___x_1604_; 
v_v_1603_ = lean_array_uget_borrowed(v_bs_1594_, v_i_1593_);
lean_inc(v_v_1603_);
v___x_1604_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_1603_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1606_; lean_object* v_bs_x27_1607_; size_t v___x_1608_; size_t v___x_1609_; lean_object* v___x_1610_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v___x_1606_ = lean_unsigned_to_nat(0u);
v_bs_x27_1607_ = lean_array_uset(v_bs_1594_, v_i_1593_, v___x_1606_);
v___x_1608_ = ((size_t)1ULL);
v___x_1609_ = lean_usize_add(v_i_1593_, v___x_1608_);
v___x_1610_ = lean_array_uset(v_bs_x27_1607_, v_i_1593_, v_a_1605_);
v_i_1593_ = v___x_1609_;
v_bs_1594_ = v___x_1610_;
goto _start;
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v_bs_1594_);
v_a_1612_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1604_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1604_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_1620_, lean_object* v_i_1621_, lean_object* v_bs_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
size_t v_sz_boxed_1629_; size_t v_i_boxed_1630_; lean_object* v_res_1631_; 
v_sz_boxed_1629_ = lean_unbox_usize(v_sz_1620_);
lean_dec(v_sz_1620_);
v_i_boxed_1630_ = lean_unbox_usize(v_i_1621_);
lean_dec(v_i_1621_);
v_res_1631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_1629_, v_i_boxed_1630_, v_bs_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object* v_x_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object* v_t_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_root_1647_; lean_object* v_tail_1648_; lean_object* v_size_1649_; size_t v_shift_1650_; lean_object* v_tailOff_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1687_; 
v_root_1647_ = lean_ctor_get(v_t_1640_, 0);
v_tail_1648_ = lean_ctor_get(v_t_1640_, 1);
v_size_1649_ = lean_ctor_get(v_t_1640_, 2);
v_shift_1650_ = lean_ctor_get_usize(v_t_1640_, 4);
v_tailOff_1651_ = lean_ctor_get(v_t_1640_, 3);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_t_1640_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1653_ = v_t_1640_;
v_isShared_1654_ = v_isSharedCheck_1687_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_tailOff_1651_);
lean_inc(v_size_1649_);
lean_inc(v_tail_1648_);
lean_inc(v_root_1647_);
lean_dec(v_t_1640_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1687_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_1647_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; size_t v_sz_1657_; size_t v___x_1658_; lean_object* v___x_1659_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v_sz_1657_ = lean_array_size(v_tail_1648_);
v___x_1658_ = ((size_t)0ULL);
v___x_1659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1657_, v___x_1658_, v_tail_1648_, v___y_1641_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1670_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v_a_1660_);
lean_ctor_set(v___x_1653_, 0, v_a_1656_);
v___x_1665_ = v___x_1653_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1656_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_a_1660_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_size_1649_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_tailOff_1651_);
lean_ctor_set_usize(v_reuseFailAlloc_1669_, 4, v_shift_1650_);
v___x_1665_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1665_);
v___x_1667_ = v___x_1662_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_a_1656_);
lean_del_object(v___x_1653_);
lean_dec(v_tailOff_1651_);
lean_dec(v_size_1649_);
v_a_1671_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1659_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1659_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_del_object(v___x_1653_);
lean_dec(v_tailOff_1651_);
lean_dec(v_size_1649_);
lean_dec_ref(v_tail_1648_);
v_a_1679_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1655_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1655_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object* v_t_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object* v_ctx_1696_, lean_object* v_targetUses_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_decls_1703_; lean_object* v_fvarIdToDecl_1704_; lean_object* v_auxDeclToFullName_1705_; lean_object* v_size_1706_; lean_object* v_decls_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_decls_1703_ = lean_ctor_get(v_ctx_1696_, 1);
lean_inc_ref(v_decls_1703_);
v_fvarIdToDecl_1704_ = lean_ctor_get(v_ctx_1696_, 0);
lean_inc_ref(v_fvarIdToDecl_1704_);
v_auxDeclToFullName_1705_ = lean_ctor_get(v_ctx_1696_, 2);
lean_inc(v_auxDeclToFullName_1705_);
v_size_1706_ = lean_ctor_get(v_decls_1703_, 2);
v_decls_1707_ = lean_mk_empty_array_with_capacity(v_size_1706_);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v_decls_1707_);
lean_ctor_set(v___x_1708_, 1, v_targetUses_1697_);
v___x_1709_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_ctx_1696_, v___x_1708_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v_fst_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v_fst_1711_ = lean_ctor_get(v_a_1710_, 0);
lean_inc(v_fst_1711_);
lean_dec(v_a_1710_);
v___x_1712_ = lean_st_mk_ref(v_fst_1711_);
v___x_1713_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_1703_, v___x_1712_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1723_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1723_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1723_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1718_ = lean_st_ref_get(v___x_1712_);
lean_dec(v___x_1712_);
lean_dec(v___x_1718_);
v___x_1719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1719_, 0, v_fvarIdToDecl_1704_);
lean_ctor_set(v___x_1719_, 1, v_a_1714_);
lean_ctor_set(v___x_1719_, 2, v_auxDeclToFullName_1705_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1719_);
v___x_1721_ = v___x_1716_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v___x_1712_);
lean_dec(v_auxDeclToFullName_1705_);
lean_dec_ref(v_fvarIdToDecl_1704_);
v_a_1724_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1713_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1713_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v_auxDeclToFullName_1705_);
lean_dec_ref(v_fvarIdToDecl_1704_);
lean_dec_ref(v_decls_1703_);
v_a_1732_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1709_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1709_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object* v_ctx_1740_, lean_object* v_targetUses_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1740_, v_targetUses_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t v_sz_1748_, size_t v_i_1749_, lean_object* v_bs_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1748_, v_i_1749_, v_bs_1750_, v___y_1751_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object* v_sz_1758_, lean_object* v_i_1759_, lean_object* v_bs_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
size_t v_sz_boxed_1767_; size_t v_i_boxed_1768_; lean_object* v_res_1769_; 
v_sz_boxed_1767_ = lean_unbox_usize(v_sz_1758_);
lean_dec(v_sz_1758_);
v_i_boxed_1768_ = lean_unbox_usize(v_i_1759_);
lean_dec(v_i_1759_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_1767_, v_i_boxed_1768_, v_bs_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
return v_res_1769_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t v_u_1770_, lean_object* v_rhs_1771_, uint8_t v_elimTrivial_1772_){
_start:
{
uint8_t v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = 2;
v___x_1774_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_1770_, v___x_1773_);
if (v___x_1774_ == 0)
{
return v___x_1774_;
}
else
{
if (v_elimTrivial_1772_ == 0)
{
return v___x_1774_;
}
else
{
uint8_t v___x_1775_; 
v___x_1775_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_1771_);
if (v___x_1775_ == 0)
{
return v___x_1774_;
}
else
{
uint8_t v___x_1776_; 
v___x_1776_ = 0;
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object* v_u_1777_, lean_object* v_rhs_1778_, lean_object* v_elimTrivial_1779_){
_start:
{
uint8_t v_u_boxed_1780_; uint8_t v_elimTrivial_boxed_1781_; uint8_t v_res_1782_; lean_object* v_r_1783_; 
v_u_boxed_1780_ = lean_unbox(v_u_1777_);
v_elimTrivial_boxed_1781_ = lean_unbox(v_elimTrivial_1779_);
v_res_1782_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_1780_, v_rhs_1778_, v_elimTrivial_boxed_1781_);
lean_dec_ref(v_rhs_1778_);
v_r_1783_ = lean_box(v_res_1782_);
return v_r_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t v_elimTrivial_1786_, lean_object* v_e_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
if (lean_obj_tag(v_e_1787_) == 8)
{
lean_object* v_type_1794_; 
v_type_1794_ = lean_ctor_get(v_e_1787_, 1);
if (lean_obj_tag(v_type_1794_) == 10)
{
lean_object* v_value_1795_; lean_object* v_body_1796_; lean_object* v_data_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v_uses_1801_; uint8_t v___x_1802_; 
v_value_1795_ = lean_ctor_get(v_e_1787_, 2);
v_body_1796_ = lean_ctor_get(v_e_1787_, 3);
v_data_1797_ = lean_ctor_get(v_type_1794_, 0);
v___x_1798_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1799_ = lean_unsigned_to_nat(2u);
v___x_1800_ = l_Lean_KVMap_getNat(v_data_1797_, v___x_1798_, v___x_1799_);
v_uses_1801_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_1800_);
lean_dec(v___x_1800_);
v___x_1802_ = l_Lean_Elab_Tactic_Do_doNotDup(v_uses_1801_, v_value_1795_, v_elimTrivial_1786_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = lean_expr_instantiate1(v_body_1796_, v_value_1795_);
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
return v___x_1809_;
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object* v_elimTrivial_1812_, lean_object* v_e_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
uint8_t v_elimTrivial_boxed_1820_; lean_object* v_res_1821_; 
v_elimTrivial_boxed_1820_ = lean_unbox(v_elimTrivial_1812_);
v_res_1821_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_boxed_1820_, v_e_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v_e_1813_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object* v_e_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v_e_1822_);
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object* v_e_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
return v_res_1838_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = l_Lean_maxRecDepthErrorMessage;
v___x_1845_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_1847_ = l_Lean_MessageData_ofFormat(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_1849_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_1850_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v___x_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_1851_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_ref_1851_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1856_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object* v_x_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___y_1868_; lean_object* v_toCold_1877_; lean_object* v_currRecDepth_1878_; lean_object* v_ref_1879_; uint8_t v_diag_1880_; uint8_t v_suppressElabErrors_1881_; lean_object* v_maxRecDepth_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v_toCold_1877_ = lean_ctor_get(v___y_1864_, 0);
v_currRecDepth_1878_ = lean_ctor_get(v___y_1864_, 1);
v_ref_1879_ = lean_ctor_get(v___y_1864_, 2);
v_diag_1880_ = lean_ctor_get_uint8(v___y_1864_, sizeof(void*)*3);
v_suppressElabErrors_1881_ = lean_ctor_get_uint8(v___y_1864_, sizeof(void*)*3 + 1);
v_maxRecDepth_1887_ = lean_ctor_get(v_toCold_1877_, 3);
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = lean_nat_dec_eq(v_maxRecDepth_1887_, v___x_1888_);
if (v___x_1889_ == 0)
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_nat_dec_eq(v_currRecDepth_1878_, v_maxRecDepth_1887_);
if (v___x_1890_ == 0)
{
goto v___jp_1882_;
}
else
{
lean_object* v___x_1891_; 
lean_dec_ref(v_x_1859_);
lean_inc(v_ref_1879_);
v___x_1891_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1879_);
v___y_1868_ = v___x_1891_;
goto v___jp_1867_;
}
}
else
{
goto v___jp_1882_;
}
v___jp_1867_:
{
if (lean_obj_tag(v___y_1868_) == 0)
{
return v___y_1868_;
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
v_a_1869_ = lean_ctor_get(v___y_1868_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___y_1868_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___y_1868_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___y_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
v___jp_1882_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1883_ = lean_unsigned_to_nat(1u);
v___x_1884_ = lean_nat_add(v_currRecDepth_1878_, v___x_1883_);
lean_inc(v_ref_1879_);
lean_inc_ref(v_toCold_1877_);
v___x_1885_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1885_, 0, v_toCold_1877_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
lean_ctor_set(v___x_1885_, 2, v_ref_1879_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*3, v_diag_1880_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*3 + 1, v_suppressElabErrors_1881_);
lean_inc(v___y_1865_);
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
lean_inc(v___y_1861_);
lean_inc(v___y_1860_);
v___x_1886_ = lean_apply_7(v_x_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___x_1885_, v___y_1865_, lean_box(0));
v___y_1868_ = v___x_1886_;
goto v___jp_1867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec(v___y_1893_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_1901_, lean_object* v_x_1902_){
_start:
{
if (lean_obj_tag(v_x_1902_) == 0)
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_box(0);
return v___x_1903_;
}
else
{
lean_object* v_key_1904_; lean_object* v_value_1905_; lean_object* v_tail_1906_; uint8_t v___x_1907_; 
v_key_1904_ = lean_ctor_get(v_x_1902_, 0);
v_value_1905_ = lean_ctor_get(v_x_1902_, 1);
v_tail_1906_ = lean_ctor_get(v_x_1902_, 2);
v___x_1907_ = l_Lean_ExprStructEq_beq(v_key_1904_, v_a_1901_);
if (v___x_1907_ == 0)
{
v_x_1902_ = v_tail_1906_;
goto _start;
}
else
{
lean_object* v___x_1909_; 
lean_inc(v_value_1905_);
v___x_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_value_1905_);
return v___x_1909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_1910_, lean_object* v_x_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1910_, v_x_1911_);
lean_dec(v_x_1911_);
lean_dec_ref(v_a_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_m_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v_buckets_1915_; lean_object* v___x_1916_; uint64_t v___x_1917_; uint64_t v___x_1918_; uint64_t v___x_1919_; uint64_t v_fold_1920_; uint64_t v___x_1921_; uint64_t v___x_1922_; uint64_t v___x_1923_; size_t v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_buckets_1915_ = lean_ctor_get(v_m_1913_, 1);
v___x_1916_ = lean_array_get_size(v_buckets_1915_);
v___x_1917_ = l_Lean_ExprStructEq_hash(v_a_1914_);
v___x_1918_ = 32ULL;
v___x_1919_ = lean_uint64_shift_right(v___x_1917_, v___x_1918_);
v_fold_1920_ = lean_uint64_xor(v___x_1917_, v___x_1919_);
v___x_1921_ = 16ULL;
v___x_1922_ = lean_uint64_shift_right(v_fold_1920_, v___x_1921_);
v___x_1923_ = lean_uint64_xor(v_fold_1920_, v___x_1922_);
v___x_1924_ = lean_uint64_to_usize(v___x_1923_);
v___x_1925_ = lean_usize_of_nat(v___x_1916_);
v___x_1926_ = ((size_t)1ULL);
v___x_1927_ = lean_usize_sub(v___x_1925_, v___x_1926_);
v___x_1928_ = lean_usize_land(v___x_1924_, v___x_1927_);
v___x_1929_ = lean_array_uget_borrowed(v_buckets_1915_, v___x_1928_);
v___x_1930_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1914_, v___x_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_1931_, v_a_1932_);
lean_dec_ref(v_a_1932_);
lean_dec_ref(v_m_1931_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v_b_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; 
lean_inc(v___y_1941_);
lean_inc_ref(v___y_1940_);
lean_inc(v___y_1939_);
lean_inc_ref(v___y_1938_);
lean_inc(v___y_1936_);
lean_inc(v___y_1935_);
v___x_1943_ = lean_apply_8(v_k_1934_, v_b_1937_, v___y_1935_, v___y_1936_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, lean_box(0));
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v_b_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1944_, v___y_1945_, v___y_1946_, v_b_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1946_);
lean_dec(v___y_1945_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_1954_, lean_object* v_type_1955_, lean_object* v_val_1956_, lean_object* v_k_1957_, uint8_t v_nondep_1958_, uint8_t v_kind_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___f_1967_; lean_object* v___x_1968_; 
lean_inc(v___y_1961_);
lean_inc(v___y_1960_);
v___f_1967_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1967_, 0, v_k_1957_);
lean_closure_set(v___f_1967_, 1, v___y_1960_);
lean_closure_set(v___f_1967_, 2, v___y_1961_);
v___x_1968_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1954_, v_type_1955_, v_val_1956_, v___f_1967_, v_nondep_1958_, v_kind_1959_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1968_) == 0)
{
return v___x_1968_;
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_1977_, lean_object* v_type_1978_, lean_object* v_val_1979_, lean_object* v_k_1980_, lean_object* v_nondep_1981_, lean_object* v_kind_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
uint8_t v_nondep_boxed_1990_; uint8_t v_kind_boxed_1991_; lean_object* v_res_1992_; 
v_nondep_boxed_1990_ = lean_unbox(v_nondep_1981_);
v_kind_boxed_1991_ = lean_unbox(v_kind_1982_);
v_res_1992_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1977_, v_type_1978_, v_val_1979_, v_k_1980_, v_nondep_boxed_1990_, v_kind_boxed_1991_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec(v___y_1983_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_1993_, uint8_t v_bi_1994_, lean_object* v_type_1995_, lean_object* v_k_1996_, uint8_t v_kind_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v___f_2005_; lean_object* v___x_2006_; 
lean_inc(v___y_1999_);
lean_inc(v___y_1998_);
v___f_2005_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2005_, 0, v_k_1996_);
lean_closure_set(v___f_2005_, 1, v___y_1998_);
lean_closure_set(v___f_2005_, 2, v___y_1999_);
v___x_2006_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1993_, v_bi_1994_, v_type_1995_, v___f_2005_, v_kind_1997_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2006_) == 0)
{
return v___x_2006_;
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_2015_, lean_object* v_bi_2016_, lean_object* v_type_2017_, lean_object* v_k_2018_, lean_object* v_kind_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v_bi_boxed_2027_; uint8_t v_kind_boxed_2028_; lean_object* v_res_2029_; 
v_bi_boxed_2027_ = lean_unbox(v_bi_2016_);
v_kind_boxed_2028_ = lean_unbox(v_kind_2019_);
v_res_2029_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2015_, v_bi_boxed_2027_, v_type_2017_, v_k_2018_, v_kind_boxed_2028_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec(v___y_2020_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2030_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2046_, lean_object* v_x_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_apply_1(v_x_2047_, lean_box(0));
v___x_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2056_, lean_object* v_x_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2056_, v_x_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
if (lean_obj_tag(v_x_2066_) == 0)
{
return v_x_2065_;
}
else
{
lean_object* v_key_2067_; lean_object* v_value_2068_; lean_object* v_tail_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2092_; 
v_key_2067_ = lean_ctor_get(v_x_2066_, 0);
v_value_2068_ = lean_ctor_get(v_x_2066_, 1);
v_tail_2069_ = lean_ctor_get(v_x_2066_, 2);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_x_2066_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2071_ = v_x_2066_;
v_isShared_2072_ = v_isSharedCheck_2092_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_tail_2069_);
lean_inc(v_value_2068_);
lean_inc(v_key_2067_);
lean_dec(v_x_2066_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2092_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; uint64_t v___x_2074_; uint64_t v___x_2075_; uint64_t v___x_2076_; uint64_t v_fold_2077_; uint64_t v___x_2078_; uint64_t v___x_2079_; uint64_t v___x_2080_; size_t v___x_2081_; size_t v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; size_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2073_ = lean_array_get_size(v_x_2065_);
v___x_2074_ = l_Lean_ExprStructEq_hash(v_key_2067_);
v___x_2075_ = 32ULL;
v___x_2076_ = lean_uint64_shift_right(v___x_2074_, v___x_2075_);
v_fold_2077_ = lean_uint64_xor(v___x_2074_, v___x_2076_);
v___x_2078_ = 16ULL;
v___x_2079_ = lean_uint64_shift_right(v_fold_2077_, v___x_2078_);
v___x_2080_ = lean_uint64_xor(v_fold_2077_, v___x_2079_);
v___x_2081_ = lean_uint64_to_usize(v___x_2080_);
v___x_2082_ = lean_usize_of_nat(v___x_2073_);
v___x_2083_ = ((size_t)1ULL);
v___x_2084_ = lean_usize_sub(v___x_2082_, v___x_2083_);
v___x_2085_ = lean_usize_land(v___x_2081_, v___x_2084_);
v___x_2086_ = lean_array_uget_borrowed(v_x_2065_, v___x_2085_);
lean_inc(v___x_2086_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 2, v___x_2086_);
v___x_2088_ = v___x_2071_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_key_2067_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_value_2068_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_array_uset(v_x_2065_, v___x_2085_, v___x_2088_);
v_x_2065_ = v___x_2089_;
v_x_2066_ = v_tail_2069_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_2093_, lean_object* v_source_2094_, lean_object* v_target_2095_){
_start:
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = lean_array_get_size(v_source_2094_);
v___x_2097_ = lean_nat_dec_lt(v_i_2093_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_dec_ref(v_source_2094_);
lean_dec(v_i_2093_);
return v_target_2095_;
}
else
{
lean_object* v_es_2098_; lean_object* v___x_2099_; lean_object* v_source_2100_; lean_object* v_target_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_es_2098_ = lean_array_fget(v_source_2094_, v_i_2093_);
v___x_2099_ = lean_box(0);
v_source_2100_ = lean_array_fset(v_source_2094_, v_i_2093_, v___x_2099_);
v_target_2101_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_2095_, v_es_2098_);
v___x_2102_ = lean_unsigned_to_nat(1u);
v___x_2103_ = lean_nat_add(v_i_2093_, v___x_2102_);
lean_dec(v_i_2093_);
v_i_2093_ = v___x_2103_;
v_source_2094_ = v_source_2100_;
v_target_2095_ = v_target_2101_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_2105_){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v_nbuckets_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2106_ = lean_array_get_size(v_data_2105_);
v___x_2107_ = lean_unsigned_to_nat(2u);
v_nbuckets_2108_ = lean_nat_mul(v___x_2106_, v___x_2107_);
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = lean_box(0);
v___x_2111_ = lean_mk_array(v_nbuckets_2108_, v___x_2110_);
v___x_2112_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_2109_, v_data_2105_, v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_2113_, lean_object* v_b_2114_, lean_object* v_x_2115_){
_start:
{
if (lean_obj_tag(v_x_2115_) == 0)
{
lean_dec(v_b_2114_);
lean_dec_ref(v_a_2113_);
return v_x_2115_;
}
else
{
lean_object* v_key_2116_; lean_object* v_value_2117_; lean_object* v_tail_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2130_; 
v_key_2116_ = lean_ctor_get(v_x_2115_, 0);
v_value_2117_ = lean_ctor_get(v_x_2115_, 1);
v_tail_2118_ = lean_ctor_get(v_x_2115_, 2);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_x_2115_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2120_ = v_x_2115_;
v_isShared_2121_ = v_isSharedCheck_2130_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_tail_2118_);
lean_inc(v_value_2117_);
lean_inc(v_key_2116_);
lean_dec(v_x_2115_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2130_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
uint8_t v___x_2122_; 
v___x_2122_ = l_Lean_ExprStructEq_beq(v_key_2116_, v_a_2113_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2113_, v_b_2114_, v_tail_2118_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 2, v___x_2123_);
v___x_2125_ = v___x_2120_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_key_2116_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_value_2117_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
else
{
lean_object* v___x_2128_; 
lean_dec(v_value_2117_);
lean_dec(v_key_2116_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v_b_2114_);
lean_ctor_set(v___x_2120_, 0, v_a_2113_);
v___x_2128_ = v___x_2120_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2113_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_b_2114_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_tail_2118_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_2131_, lean_object* v_x_2132_){
_start:
{
if (lean_obj_tag(v_x_2132_) == 0)
{
uint8_t v___x_2133_; 
v___x_2133_ = 0;
return v___x_2133_;
}
else
{
lean_object* v_key_2134_; lean_object* v_tail_2135_; uint8_t v___x_2136_; 
v_key_2134_ = lean_ctor_get(v_x_2132_, 0);
v_tail_2135_ = lean_ctor_get(v_x_2132_, 2);
v___x_2136_ = l_Lean_ExprStructEq_beq(v_key_2134_, v_a_2131_);
if (v___x_2136_ == 0)
{
v_x_2132_ = v_tail_2135_;
goto _start;
}
else
{
return v___x_2136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_2138_, lean_object* v_x_2139_){
_start:
{
uint8_t v_res_2140_; lean_object* v_r_2141_; 
v_res_2140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2138_, v_x_2139_);
lean_dec(v_x_2139_);
lean_dec_ref(v_a_2138_);
v_r_2141_ = lean_box(v_res_2140_);
return v_r_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2142_, lean_object* v_a_2143_, lean_object* v_b_2144_){
_start:
{
lean_object* v_size_2145_; lean_object* v_buckets_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2189_; 
v_size_2145_ = lean_ctor_get(v_m_2142_, 0);
v_buckets_2146_ = lean_ctor_get(v_m_2142_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_m_2142_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2148_ = v_m_2142_;
v_isShared_2149_ = v_isSharedCheck_2189_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_buckets_2146_);
lean_inc(v_size_2145_);
lean_dec(v_m_2142_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2189_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; uint64_t v___x_2151_; uint64_t v___x_2152_; uint64_t v___x_2153_; uint64_t v_fold_2154_; uint64_t v___x_2155_; uint64_t v___x_2156_; uint64_t v___x_2157_; size_t v___x_2158_; size_t v___x_2159_; size_t v___x_2160_; size_t v___x_2161_; size_t v___x_2162_; lean_object* v_bkt_2163_; uint8_t v___x_2164_; 
v___x_2150_ = lean_array_get_size(v_buckets_2146_);
v___x_2151_ = l_Lean_ExprStructEq_hash(v_a_2143_);
v___x_2152_ = 32ULL;
v___x_2153_ = lean_uint64_shift_right(v___x_2151_, v___x_2152_);
v_fold_2154_ = lean_uint64_xor(v___x_2151_, v___x_2153_);
v___x_2155_ = 16ULL;
v___x_2156_ = lean_uint64_shift_right(v_fold_2154_, v___x_2155_);
v___x_2157_ = lean_uint64_xor(v_fold_2154_, v___x_2156_);
v___x_2158_ = lean_uint64_to_usize(v___x_2157_);
v___x_2159_ = lean_usize_of_nat(v___x_2150_);
v___x_2160_ = ((size_t)1ULL);
v___x_2161_ = lean_usize_sub(v___x_2159_, v___x_2160_);
v___x_2162_ = lean_usize_land(v___x_2158_, v___x_2161_);
v_bkt_2163_ = lean_array_uget_borrowed(v_buckets_2146_, v___x_2162_);
v___x_2164_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2143_, v_bkt_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v_size_x27_2166_; lean_object* v___x_2167_; lean_object* v_buckets_x27_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2165_ = lean_unsigned_to_nat(1u);
v_size_x27_2166_ = lean_nat_add(v_size_2145_, v___x_2165_);
lean_dec(v_size_2145_);
lean_inc(v_bkt_2163_);
v___x_2167_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2167_, 0, v_a_2143_);
lean_ctor_set(v___x_2167_, 1, v_b_2144_);
lean_ctor_set(v___x_2167_, 2, v_bkt_2163_);
v_buckets_x27_2168_ = lean_array_uset(v_buckets_2146_, v___x_2162_, v___x_2167_);
v___x_2169_ = lean_unsigned_to_nat(4u);
v___x_2170_ = lean_nat_mul(v_size_x27_2166_, v___x_2169_);
v___x_2171_ = lean_unsigned_to_nat(3u);
v___x_2172_ = lean_nat_div(v___x_2170_, v___x_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_array_get_size(v_buckets_x27_2168_);
v___x_2174_ = lean_nat_dec_le(v___x_2172_, v___x_2173_);
lean_dec(v___x_2172_);
if (v___x_2174_ == 0)
{
lean_object* v_val_2175_; lean_object* v___x_2177_; 
v_val_2175_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_2168_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v_val_2175_);
lean_ctor_set(v___x_2148_, 0, v_size_x27_2166_);
v___x_2177_ = v___x_2148_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_size_x27_2166_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_val_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
else
{
lean_object* v___x_2180_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v_buckets_x27_2168_);
lean_ctor_set(v___x_2148_, 0, v_size_x27_2166_);
v___x_2180_ = v___x_2148_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_size_x27_2166_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_buckets_x27_2168_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
else
{
lean_object* v___x_2182_; lean_object* v_buckets_x27_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
lean_inc(v_bkt_2163_);
v___x_2182_ = lean_box(0);
v_buckets_x27_2183_ = lean_array_uset(v_buckets_2146_, v___x_2162_, v___x_2182_);
v___x_2184_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2143_, v_b_2144_, v_bkt_2163_);
v___x_2185_ = lean_array_uset(v_buckets_x27_2183_, v___x_2162_, v___x_2184_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v___x_2185_);
v___x_2187_ = v___x_2148_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_size_2145_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2190_, lean_object* v_e_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2194_ = lean_st_ref_take(v_a_2190_);
v___x_2195_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2194_, v_e_2191_, v_a_2192_);
v___x_2196_ = lean_st_ref_put(v_a_2190_, v___x_2195_);
v___x_2197_ = lean_box(0);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2198_, lean_object* v_e_2199_, lean_object* v_a_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2198_, v_e_2199_, v_a_2200_);
lean_dec(v_a_2198_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_2206_, lean_object* v_pre_2207_, lean_object* v_post_2208_, uint8_t v_usedLetOnly_2209_, uint8_t v_skipConstInApp_2210_, uint8_t v_skipInstances_2211_, lean_object* v_body_2212_, lean_object* v_x_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_array_push(v_fvars_2206_, v_x_2213_);
v___x_2222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2207_, v_post_2208_, v_usedLetOnly_2209_, v_skipConstInApp_2210_, v_skipInstances_2211_, v___x_2221_, v_body_2212_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_2223_, lean_object* v_pre_2224_, lean_object* v_post_2225_, lean_object* v_usedLetOnly_2226_, lean_object* v_skipConstInApp_2227_, lean_object* v_skipInstances_2228_, lean_object* v_body_2229_, lean_object* v_x_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
uint8_t v_usedLetOnly_boxed_2238_; uint8_t v_skipConstInApp_boxed_2239_; uint8_t v_skipInstances_boxed_2240_; lean_object* v_res_2241_; 
v_usedLetOnly_boxed_2238_ = lean_unbox(v_usedLetOnly_2226_);
v_skipConstInApp_boxed_2239_ = lean_unbox(v_skipConstInApp_2227_);
v_skipInstances_boxed_2240_ = lean_unbox(v_skipInstances_2228_);
v_res_2241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2223_, v_pre_2224_, v_post_2225_, v_usedLetOnly_boxed_2238_, v_skipConstInApp_boxed_2239_, v_skipInstances_boxed_2240_, v_body_2229_, v_x_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec(v___y_2231_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object* v_pre_2242_, lean_object* v_post_2243_, uint8_t v_usedLetOnly_2244_, uint8_t v_skipConstInApp_2245_, uint8_t v_skipInstances_2246_, lean_object* v_e_2247_, lean_object* v_a_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
lean_inc_ref(v_post_2243_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
lean_inc_ref(v_e_2247_);
v___x_2255_ = lean_apply_7(v_post_2243_, v_e_2247_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, lean_box(0));
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2274_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2274_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2274_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
switch(lean_obj_tag(v_a_2256_))
{
case 0:
{
lean_object* v_e_2260_; lean_object* v___x_2262_; 
lean_dec_ref(v_e_2247_);
lean_dec_ref(v_post_2243_);
lean_dec_ref(v_pre_2242_);
v_e_2260_ = lean_ctor_get(v_a_2256_, 0);
lean_inc_ref(v_e_2260_);
lean_dec_ref_known(v_a_2256_, 1);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v_e_2260_);
v___x_2262_ = v___x_2258_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_e_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
case 1:
{
lean_object* v_e_2264_; lean_object* v___x_2265_; 
lean_del_object(v___x_2258_);
lean_dec_ref(v_e_2247_);
v_e_2264_ = lean_ctor_get(v_a_2256_, 0);
lean_inc_ref(v_e_2264_);
lean_dec_ref_known(v_a_2256_, 1);
v___x_2265_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2242_, v_post_2243_, v_usedLetOnly_2244_, v_skipConstInApp_2245_, v_skipInstances_2246_, v_e_2264_, v_a_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v___x_2265_;
}
default: 
{
lean_object* v_e_x3f_2266_; 
lean_dec_ref(v_post_2243_);
lean_dec_ref(v_pre_2242_);
v_e_x3f_2266_ = lean_ctor_get(v_a_2256_, 0);
lean_inc(v_e_x3f_2266_);
lean_dec_ref_known(v_a_2256_, 1);
if (lean_obj_tag(v_e_x3f_2266_) == 0)
{
lean_object* v___x_2268_; 
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v_e_2247_);
v___x_2268_ = v___x_2258_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_e_2247_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
else
{
lean_object* v_val_2270_; lean_object* v___x_2272_; 
lean_dec_ref(v_e_2247_);
v_val_2270_ = lean_ctor_get(v_e_x3f_2266_, 0);
lean_inc(v_val_2270_);
lean_dec_ref_known(v_e_x3f_2266_, 1);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v_val_2270_);
v___x_2272_ = v___x_2258_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_val_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec_ref(v_e_2247_);
lean_dec_ref(v_post_2243_);
lean_dec_ref(v_pre_2242_);
v_a_2275_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2255_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2255_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object* v_pre_2283_, lean_object* v_post_2284_, uint8_t v_usedLetOnly_2285_, uint8_t v_skipConstInApp_2286_, uint8_t v_skipInstances_2287_, lean_object* v_fvars_2288_, lean_object* v_e_2289_, lean_object* v_a_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
if (lean_obj_tag(v_e_2289_) == 6)
{
lean_object* v_binderName_2297_; lean_object* v_binderType_2298_; lean_object* v_body_2299_; uint8_t v_binderInfo_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_binderName_2297_ = lean_ctor_get(v_e_2289_, 0);
lean_inc(v_binderName_2297_);
v_binderType_2298_ = lean_ctor_get(v_e_2289_, 1);
lean_inc_ref(v_binderType_2298_);
v_body_2299_ = lean_ctor_get(v_e_2289_, 2);
lean_inc_ref(v_body_2299_);
v_binderInfo_2300_ = lean_ctor_get_uint8(v_e_2289_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2289_, 3);
v___x_2301_ = lean_expr_instantiate_rev(v_binderType_2298_, v_fvars_2288_);
lean_dec_ref(v_binderType_2298_);
lean_inc_ref(v_post_2284_);
lean_inc_ref(v_pre_2283_);
v___x_2302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2283_, v_post_2284_, v_usedLetOnly_2285_, v_skipConstInApp_2286_, v_skipInstances_2287_, v___x_2301_, v_a_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___f_2307_; uint8_t v___x_2308_; lean_object* v___x_2309_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = lean_box(v_usedLetOnly_2285_);
v___x_2305_ = lean_box(v_skipConstInApp_2286_);
v___x_2306_ = lean_box(v_skipInstances_2287_);
v___f_2307_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2307_, 0, v_fvars_2288_);
lean_closure_set(v___f_2307_, 1, v_pre_2283_);
lean_closure_set(v___f_2307_, 2, v_post_2284_);
lean_closure_set(v___f_2307_, 3, v___x_2304_);
lean_closure_set(v___f_2307_, 4, v___x_2305_);
lean_closure_set(v___f_2307_, 5, v___x_2306_);
lean_closure_set(v___f_2307_, 6, v_body_2299_);
v___x_2308_ = 0;
v___x_2309_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2297_, v_binderInfo_2300_, v_a_2303_, v___f_2307_, v___x_2308_, v_a_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2309_;
}
else
{
lean_dec_ref(v_body_2299_);
lean_dec(v_binderName_2297_);
lean_dec_ref(v_fvars_2288_);
lean_dec_ref(v_post_2284_);
lean_dec_ref(v_pre_2283_);
return v___x_2302_;
}
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_expr_instantiate_rev(v_e_2289_, v_fvars_2288_);
lean_dec_ref(v_e_2289_);
lean_inc_ref(v_post_2284_);
lean_inc_ref(v_pre_2283_);
v___x_2311_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2283_, v_post_2284_, v_usedLetOnly_2285_, v_skipConstInApp_2286_, v_skipInstances_2287_, v___x_2310_, v_a_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; uint8_t v___x_2313_; uint8_t v___x_2314_; uint8_t v___x_2315_; lean_object* v___x_2316_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = 0;
v___x_2314_ = 1;
v___x_2315_ = 1;
v___x_2316_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2288_, v_a_2312_, v___x_2313_, v_usedLetOnly_2285_, v___x_2313_, v___x_2314_, v___x_2315_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec_ref(v_fvars_2288_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2283_, v_post_2284_, v_usedLetOnly_2285_, v_skipConstInApp_2286_, v_skipInstances_2287_, v_a_2317_, v_a_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2318_;
}
else
{
lean_dec_ref(v_post_2284_);
lean_dec_ref(v_pre_2283_);
return v___x_2316_;
}
}
else
{
lean_dec_ref(v_fvars_2288_);
lean_dec_ref(v_post_2284_);
lean_dec_ref(v_pre_2283_);
return v___x_2311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_2319_, lean_object* v_pre_2320_, lean_object* v_post_2321_, uint8_t v_usedLetOnly_2322_, uint8_t v_skipConstInApp_2323_, uint8_t v_skipInstances_2324_, lean_object* v_body_2325_, lean_object* v_x_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_array_push(v_fvars_2319_, v_x_2326_);
v___x_2335_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2320_, v_post_2321_, v_usedLetOnly_2322_, v_skipConstInApp_2323_, v_skipInstances_2324_, v___x_2334_, v_body_2325_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_2336_, lean_object* v_pre_2337_, lean_object* v_post_2338_, lean_object* v_usedLetOnly_2339_, lean_object* v_skipConstInApp_2340_, lean_object* v_skipInstances_2341_, lean_object* v_body_2342_, lean_object* v_x_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
uint8_t v_usedLetOnly_boxed_2351_; uint8_t v_skipConstInApp_boxed_2352_; uint8_t v_skipInstances_boxed_2353_; lean_object* v_res_2354_; 
v_usedLetOnly_boxed_2351_ = lean_unbox(v_usedLetOnly_2339_);
v_skipConstInApp_boxed_2352_ = lean_unbox(v_skipConstInApp_2340_);
v_skipInstances_boxed_2353_ = lean_unbox(v_skipInstances_2341_);
v_res_2354_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2336_, v_pre_2337_, v_post_2338_, v_usedLetOnly_boxed_2351_, v_skipConstInApp_boxed_2352_, v_skipInstances_boxed_2353_, v_body_2342_, v_x_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec(v___y_2344_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object* v_pre_2355_, lean_object* v_post_2356_, uint8_t v_usedLetOnly_2357_, uint8_t v_skipConstInApp_2358_, uint8_t v_skipInstances_2359_, lean_object* v_fvars_2360_, lean_object* v_e_2361_, lean_object* v_a_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
if (lean_obj_tag(v_e_2361_) == 8)
{
lean_object* v_declName_2369_; lean_object* v_type_2370_; lean_object* v_value_2371_; lean_object* v_body_2372_; uint8_t v_nondep_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_declName_2369_ = lean_ctor_get(v_e_2361_, 0);
lean_inc(v_declName_2369_);
v_type_2370_ = lean_ctor_get(v_e_2361_, 1);
lean_inc_ref(v_type_2370_);
v_value_2371_ = lean_ctor_get(v_e_2361_, 2);
lean_inc_ref(v_value_2371_);
v_body_2372_ = lean_ctor_get(v_e_2361_, 3);
lean_inc_ref(v_body_2372_);
v_nondep_2373_ = lean_ctor_get_uint8(v_e_2361_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2361_, 4);
v___x_2374_ = lean_expr_instantiate_rev(v_type_2370_, v_fvars_2360_);
lean_dec_ref(v_type_2370_);
lean_inc_ref(v_post_2356_);
lean_inc_ref(v_pre_2355_);
v___x_2375_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2355_, v_post_2356_, v_usedLetOnly_2357_, v_skipConstInApp_2358_, v_skipInstances_2359_, v___x_2374_, v_a_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v___x_2377_ = lean_expr_instantiate_rev(v_value_2371_, v_fvars_2360_);
lean_dec_ref(v_value_2371_);
lean_inc_ref(v_post_2356_);
lean_inc_ref(v_pre_2355_);
v___x_2378_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2355_, v_post_2356_, v_usedLetOnly_2357_, v_skipConstInApp_2358_, v_skipInstances_2359_, v___x_2377_, v_a_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___f_2383_; uint8_t v___x_2384_; lean_object* v___x_2385_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2380_ = lean_box(v_usedLetOnly_2357_);
v___x_2381_ = lean_box(v_skipConstInApp_2358_);
v___x_2382_ = lean_box(v_skipInstances_2359_);
v___f_2383_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2383_, 0, v_fvars_2360_);
lean_closure_set(v___f_2383_, 1, v_pre_2355_);
lean_closure_set(v___f_2383_, 2, v_post_2356_);
lean_closure_set(v___f_2383_, 3, v___x_2380_);
lean_closure_set(v___f_2383_, 4, v___x_2381_);
lean_closure_set(v___f_2383_, 5, v___x_2382_);
lean_closure_set(v___f_2383_, 6, v_body_2372_);
v___x_2384_ = 0;
v___x_2385_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2369_, v_a_2376_, v_a_2379_, v___f_2383_, v_nondep_2373_, v___x_2384_, v_a_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
return v___x_2385_;
}
else
{
lean_dec(v_a_2376_);
lean_dec_ref(v_body_2372_);
lean_dec(v_declName_2369_);
lean_dec_ref(v_fvars_2360_);
lean_dec_ref(v_post_2356_);
lean_dec_ref(v_pre_2355_);
return v___x_2378_;
}
}
else
{
lean_dec_ref(v_body_2372_);
lean_dec_ref(v_value_2371_);
lean_dec(v_declName_2369_);
lean_dec_ref(v_fvars_2360_);
lean_dec_ref(v_post_2356_);
lean_dec_ref(v_pre_2355_);
return v___x_2375_;
}
}
else
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = lean_expr_instantiate_rev(v_e_2361_, v_fvars_2360_);
lean_dec_ref(v_e_2361_);
lean_inc_ref(v_post_2356_);
lean_inc_ref(v_pre_2355_);
v___x_2387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2355_, v_post_2356_, v_usedLetOnly_2357_, v_skipConstInApp_2358_, v_skipInstances_2359_, v___x_2386_, v_a_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; uint8_t v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2389_ = 0;
v___x_2390_ = 1;
v___x_2391_ = l_Lean_Meta_mkLetFVars(v_fvars_2360_, v_a_2388_, v_usedLetOnly_2357_, v___x_2389_, v___x_2390_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec_ref(v_fvars_2360_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2393_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2355_, v_post_2356_, v_usedLetOnly_2357_, v_skipConstInApp_2358_, v_skipInstances_2359_, v_a_2392_, v_a_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
return v___x_2393_;
}
else
{
lean_dec_ref(v_post_2356_);
lean_dec_ref(v_pre_2355_);
return v___x_2391_;
}
}
else
{
lean_dec_ref(v_fvars_2360_);
lean_dec_ref(v_post_2356_);
lean_dec_ref(v_pre_2355_);
return v___x_2387_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2394_; lean_object* v_dummy_2395_; 
v___x_2394_ = lean_box(0);
v_dummy_2395_ = l_Lean_Expr_sort___override(v___x_2394_);
return v_dummy_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object* v_pre_2396_, lean_object* v_post_2397_, uint8_t v_usedLetOnly_2398_, uint8_t v_skipConstInApp_2399_, uint8_t v_skipInstances_2400_, size_t v_sz_2401_, size_t v_i_2402_, lean_object* v_bs_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
uint8_t v___x_2411_; 
v___x_2411_ = lean_usize_dec_lt(v_i_2402_, v_sz_2401_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
lean_dec_ref(v_post_2397_);
lean_dec_ref(v_pre_2396_);
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v_bs_2403_);
return v___x_2412_;
}
else
{
lean_object* v_v_2413_; lean_object* v___x_2414_; 
v_v_2413_ = lean_array_uget_borrowed(v_bs_2403_, v_i_2402_);
lean_inc(v_v_2413_);
lean_inc_ref(v_post_2397_);
lean_inc_ref(v_pre_2396_);
v___x_2414_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2396_, v_post_2397_, v_usedLetOnly_2398_, v_skipConstInApp_2399_, v_skipInstances_2400_, v_v_2413_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2416_; lean_object* v_bs_x27_2417_; size_t v___x_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v___x_2416_ = lean_unsigned_to_nat(0u);
v_bs_x27_2417_ = lean_array_uset(v_bs_2403_, v_i_2402_, v___x_2416_);
v___x_2418_ = ((size_t)1ULL);
v___x_2419_ = lean_usize_add(v_i_2402_, v___x_2418_);
v___x_2420_ = lean_array_uset(v_bs_x27_2417_, v_i_2402_, v_a_2415_);
v_i_2402_ = v___x_2419_;
v_bs_2403_ = v___x_2420_;
goto _start;
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec_ref(v_bs_2403_);
lean_dec_ref(v_post_2397_);
lean_dec_ref(v_pre_2396_);
v_a_2422_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2414_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2414_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_2430_, lean_object* v_post_2431_, uint8_t v_usedLetOnly_2432_, uint8_t v_skipConstInApp_2433_, uint8_t v_skipInstances_2434_, lean_object* v___x_2435_, lean_object* v___y_2436_, lean_object* v_b_2437_, lean_object* v_a_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2430_, v_post_2431_, v_usedLetOnly_2432_, v_skipConstInApp_2433_, v_skipInstances_2434_, v___x_2435_, v___y_2436_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2455_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2450_ = lean_array_fset(v_b_2437_, v_a_2438_, v_a_2446_);
v___x_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2451_);
v___x_2453_ = v___x_2448_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v_b_2437_);
v_a_2456_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2445_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2445_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_2464_, lean_object* v_post_2465_, lean_object* v_usedLetOnly_2466_, lean_object* v_skipConstInApp_2467_, lean_object* v_skipInstances_2468_, lean_object* v___x_2469_, lean_object* v___y_2470_, lean_object* v_b_2471_, lean_object* v_a_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
uint8_t v_usedLetOnly_boxed_2479_; uint8_t v_skipConstInApp_boxed_2480_; uint8_t v_skipInstances_boxed_2481_; lean_object* v_res_2482_; 
v_usedLetOnly_boxed_2479_ = lean_unbox(v_usedLetOnly_2466_);
v_skipConstInApp_boxed_2480_ = lean_unbox(v_skipConstInApp_2467_);
v_skipInstances_boxed_2481_ = lean_unbox(v_skipInstances_2468_);
v_res_2482_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2464_, v_post_2465_, v_usedLetOnly_boxed_2479_, v_skipConstInApp_boxed_2480_, v_skipInstances_boxed_2481_, v___x_2469_, v___y_2470_, v_b_2471_, v_a_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec(v_a_2472_);
lean_dec(v___y_2470_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_2483_, lean_object* v___x_2484_, lean_object* v_pre_2485_, lean_object* v_post_2486_, uint8_t v_usedLetOnly_2487_, uint8_t v_skipConstInApp_2488_, uint8_t v_skipInstances_2489_, lean_object* v_a_2490_, lean_object* v_b_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___y_2500_; uint8_t v___x_2523_; 
v___x_2523_ = lean_nat_dec_lt(v_a_2490_, v_upperBound_2483_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
lean_dec(v_a_2490_);
lean_dec_ref(v_post_2486_);
lean_dec_ref(v_pre_2485_);
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_b_2491_);
return v___x_2524_;
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v___x_2525_ = lean_array_fget_borrowed(v_b_2491_, v_a_2490_);
v___x_2526_ = lean_array_get_size(v___x_2484_);
v___x_2527_ = lean_nat_dec_lt(v_a_2490_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___f_2531_; 
lean_inc(v___x_2525_);
v___x_2528_ = lean_box(v_usedLetOnly_2487_);
v___x_2529_ = lean_box(v_skipConstInApp_2488_);
v___x_2530_ = lean_box(v_skipInstances_2489_);
lean_inc(v_a_2490_);
lean_inc(v___y_2492_);
lean_inc_ref(v_post_2486_);
lean_inc_ref(v_pre_2485_);
v___f_2531_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2531_, 0, v_pre_2485_);
lean_closure_set(v___f_2531_, 1, v_post_2486_);
lean_closure_set(v___f_2531_, 2, v___x_2528_);
lean_closure_set(v___f_2531_, 3, v___x_2529_);
lean_closure_set(v___f_2531_, 4, v___x_2530_);
lean_closure_set(v___f_2531_, 5, v___x_2525_);
lean_closure_set(v___f_2531_, 6, v___y_2492_);
lean_closure_set(v___f_2531_, 7, v_b_2491_);
lean_closure_set(v___f_2531_, 8, v_a_2490_);
v___y_2500_ = v___f_2531_;
goto v___jp_2499_;
}
else
{
lean_object* v___x_2532_; uint8_t v_isInstance_2533_; 
v___x_2532_ = lean_array_fget_borrowed(v___x_2484_, v_a_2490_);
v_isInstance_2533_ = lean_ctor_get_uint8(v___x_2532_, sizeof(void*)*1 + 4);
if (v_isInstance_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___f_2537_; 
lean_inc(v___x_2525_);
v___x_2534_ = lean_box(v_usedLetOnly_2487_);
v___x_2535_ = lean_box(v_skipConstInApp_2488_);
v___x_2536_ = lean_box(v_skipInstances_2489_);
lean_inc(v_a_2490_);
lean_inc(v___y_2492_);
lean_inc_ref(v_post_2486_);
lean_inc_ref(v_pre_2485_);
v___f_2537_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2537_, 0, v_pre_2485_);
lean_closure_set(v___f_2537_, 1, v_post_2486_);
lean_closure_set(v___f_2537_, 2, v___x_2534_);
lean_closure_set(v___f_2537_, 3, v___x_2535_);
lean_closure_set(v___f_2537_, 4, v___x_2536_);
lean_closure_set(v___f_2537_, 5, v___x_2525_);
lean_closure_set(v___f_2537_, 6, v___y_2492_);
lean_closure_set(v___f_2537_, 7, v_b_2491_);
lean_closure_set(v___f_2537_, 8, v_a_2490_);
v___y_2500_ = v___f_2537_;
goto v___jp_2499_;
}
else
{
lean_object* v___x_2538_; lean_object* v___f_2539_; 
v___x_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2538_, 0, v_b_2491_);
v___f_2539_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2539_, 0, v___x_2538_);
v___y_2500_ = v___f_2539_;
goto v___jp_2499_;
}
}
}
v___jp_2499_:
{
lean_object* v___x_2501_; 
lean_inc(v___y_2497_);
lean_inc_ref(v___y_2496_);
lean_inc(v___y_2495_);
lean_inc_ref(v___y_2494_);
lean_inc(v___y_2493_);
v___x_2501_ = lean_apply_6(v___y_2500_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, lean_box(0));
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2514_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2504_ = v___x_2501_;
v_isShared_2505_ = v_isSharedCheck_2514_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2514_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
if (lean_obj_tag(v_a_2502_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2508_; 
lean_dec(v_a_2490_);
lean_dec_ref(v_post_2486_);
lean_dec_ref(v_pre_2485_);
v_a_2506_ = lean_ctor_get(v_a_2502_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v_a_2502_, 1);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v_a_2506_);
v___x_2508_ = v___x_2504_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
lean_del_object(v___x_2504_);
v_a_2510_ = lean_ctor_get(v_a_2502_, 0);
lean_inc(v_a_2510_);
lean_dec_ref_known(v_a_2502_, 1);
v___x_2511_ = lean_unsigned_to_nat(1u);
v___x_2512_ = lean_nat_add(v_a_2490_, v___x_2511_);
lean_dec(v_a_2490_);
v_a_2490_ = v___x_2512_;
v_b_2491_ = v_a_2510_;
goto _start;
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec(v_a_2490_);
lean_dec_ref(v_post_2486_);
lean_dec_ref(v_pre_2485_);
v_a_2515_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2501_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2501_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t v_skipInstances_2540_, lean_object* v_pre_2541_, lean_object* v_post_2542_, uint8_t v_usedLetOnly_2543_, uint8_t v_skipConstInApp_2544_, lean_object* v_x_2545_, lean_object* v_x_2546_, lean_object* v_x_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_f_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; 
if (lean_obj_tag(v_x_2545_) == 5)
{
lean_object* v_fn_2605_; lean_object* v_arg_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v_fn_2605_ = lean_ctor_get(v_x_2545_, 0);
lean_inc_ref(v_fn_2605_);
v_arg_2606_ = lean_ctor_get(v_x_2545_, 1);
lean_inc_ref(v_arg_2606_);
lean_dec_ref_known(v_x_2545_, 2);
v___x_2607_ = lean_array_set(v_x_2546_, v_x_2547_, v_arg_2606_);
v___x_2608_ = lean_unsigned_to_nat(1u);
v___x_2609_ = lean_nat_sub(v_x_2547_, v___x_2608_);
lean_dec(v_x_2547_);
v_x_2545_ = v_fn_2605_;
v_x_2546_ = v___x_2607_;
v_x_2547_ = v___x_2609_;
goto _start;
}
else
{
lean_dec(v_x_2547_);
if (v_skipConstInApp_2544_ == 0)
{
goto v___jp_2602_;
}
else
{
uint8_t v___x_2611_; 
v___x_2611_ = l_Lean_Expr_isConst(v_x_2545_);
if (v___x_2611_ == 0)
{
goto v___jp_2602_;
}
else
{
v_f_2556_ = v_x_2545_;
v___y_2557_ = v___y_2548_;
v___y_2558_ = v___y_2549_;
v___y_2559_ = v___y_2550_;
v___y_2560_ = v___y_2551_;
v___y_2561_ = v___y_2552_;
v___y_2562_ = v___y_2553_;
goto v___jp_2555_;
}
}
}
v___jp_2555_:
{
if (v_skipInstances_2540_ == 0)
{
size_t v_sz_2563_; size_t v___x_2564_; lean_object* v___x_2565_; 
v_sz_2563_ = lean_array_size(v_x_2546_);
v___x_2564_ = ((size_t)0ULL);
lean_inc_ref(v_post_2542_);
lean_inc_ref(v_pre_2541_);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2541_, v_post_2542_, v_usedLetOnly_2543_, v_skipConstInApp_2544_, v_skipInstances_2540_, v_sz_2563_, v___x_2564_, v_x_2546_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = l_Lean_mkAppN(v_f_2556_, v_a_2566_);
lean_dec(v_a_2566_);
v___x_2568_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2541_, v_post_2542_, v_usedLetOnly_2543_, v_skipConstInApp_2544_, v_skipInstances_2540_, v___x_2567_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
return v___x_2568_;
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref(v_f_2556_);
lean_dec_ref(v_post_2542_);
lean_dec_ref(v_pre_2541_);
v_a_2569_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2565_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2565_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = lean_array_get_size(v_x_2546_);
lean_inc_ref(v_f_2556_);
v___x_2578_ = l_Lean_Meta_getFunInfoNArgs(v_f_2556_, v___x_2577_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v_paramInfo_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2578_, 1);
v_paramInfo_2580_ = lean_ctor_get(v_a_2579_, 0);
lean_inc_ref(v_paramInfo_2580_);
lean_dec(v_a_2579_);
v___x_2581_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2542_);
lean_inc_ref(v_pre_2541_);
v___x_2582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_2577_, v_paramInfo_2580_, v_pre_2541_, v_post_2542_, v_usedLetOnly_2543_, v_skipConstInApp_2544_, v_skipInstances_2540_, v___x_2581_, v_x_2546_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec_ref(v_paramInfo_2580_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = l_Lean_mkAppN(v_f_2556_, v_a_2583_);
lean_dec(v_a_2583_);
v___x_2585_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2541_, v_post_2542_, v_usedLetOnly_2543_, v_skipConstInApp_2544_, v_skipInstances_2540_, v___x_2584_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
return v___x_2585_;
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec_ref(v_f_2556_);
lean_dec_ref(v_post_2542_);
lean_dec_ref(v_pre_2541_);
v_a_2586_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2582_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2582_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec_ref(v_f_2556_);
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_post_2542_);
lean_dec_ref(v_pre_2541_);
v_a_2594_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2578_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2578_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
v___jp_2602_:
{
lean_object* v___x_2603_; 
lean_inc_ref(v_post_2542_);
lean_inc_ref(v_pre_2541_);
v___x_2603_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2541_, v_post_2542_, v_usedLetOnly_2543_, v_skipConstInApp_2544_, v_skipInstances_2540_, v_x_2545_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v_f_2556_ = v_a_2604_;
v___y_2557_ = v___y_2548_;
v___y_2558_ = v___y_2549_;
v___y_2559_ = v___y_2550_;
v___y_2560_ = v___y_2551_;
v___y_2561_ = v___y_2552_;
v___y_2562_ = v___y_2553_;
goto v___jp_2555_;
}
else
{
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_post_2542_);
lean_dec_ref(v_pre_2541_);
return v___x_2603_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object* v___x_2612_, lean_object* v_pre_2613_, lean_object* v_e_2614_, lean_object* v_post_2615_, uint8_t v_usedLetOnly_2616_, uint8_t v_skipConstInApp_2617_, uint8_t v_skipInstances_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_Core_checkSystem(v___x_2612_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v___x_2627_; 
lean_dec_ref_known(v___x_2626_, 1);
lean_inc_ref(v_pre_2613_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v___y_2622_);
lean_inc_ref(v___y_2621_);
lean_inc(v___y_2620_);
lean_inc_ref(v_e_2614_);
v___x_2627_ = lean_apply_7(v_pre_2613_, v_e_2614_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, lean_box(0));
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2676_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2630_ = v___x_2627_;
v_isShared_2631_ = v_isSharedCheck_2676_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2627_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2676_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___y_2633_; 
switch(lean_obj_tag(v_a_2628_))
{
case 0:
{
lean_object* v_e_2668_; lean_object* v___x_2670_; 
lean_dec_ref(v_post_2615_);
lean_dec_ref(v_e_2614_);
lean_dec_ref(v_pre_2613_);
v_e_2668_ = lean_ctor_get(v_a_2628_, 0);
lean_inc_ref(v_e_2668_);
lean_dec_ref_known(v_a_2628_, 1);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v_e_2668_);
v___x_2670_ = v___x_2630_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_e_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
case 1:
{
lean_object* v_e_2672_; lean_object* v___x_2673_; 
lean_del_object(v___x_2630_);
lean_dec_ref(v_e_2614_);
v_e_2672_ = lean_ctor_get(v_a_2628_, 0);
lean_inc_ref(v_e_2672_);
lean_dec_ref_known(v_a_2628_, 1);
v___x_2673_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v_e_2672_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2673_;
}
default: 
{
lean_object* v_e_x3f_2674_; 
lean_del_object(v___x_2630_);
v_e_x3f_2674_ = lean_ctor_get(v_a_2628_, 0);
lean_inc(v_e_x3f_2674_);
lean_dec_ref_known(v_a_2628_, 1);
if (lean_obj_tag(v_e_x3f_2674_) == 0)
{
v___y_2633_ = v_e_2614_;
goto v___jp_2632_;
}
else
{
lean_object* v_val_2675_; 
lean_dec_ref(v_e_2614_);
v_val_2675_ = lean_ctor_get(v_e_x3f_2674_, 0);
lean_inc(v_val_2675_);
lean_dec_ref_known(v_e_x3f_2674_, 1);
v___y_2633_ = v_val_2675_;
goto v___jp_2632_;
}
}
}
v___jp_2632_:
{
switch(lean_obj_tag(v___y_2633_))
{
case 7:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2635_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v___x_2634_, v___y_2633_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2635_;
}
case 6:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2637_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v___x_2636_, v___y_2633_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2637_;
}
case 8:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2639_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v___x_2638_, v___y_2633_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2639_;
}
case 5:
{
lean_object* v_dummy_2640_; lean_object* v_nargs_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v_dummy_2640_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
v_nargs_2641_ = l_Lean_Expr_getAppNumArgs(v___y_2633_);
lean_inc(v_nargs_2641_);
v___x_2642_ = lean_mk_array(v_nargs_2641_, v_dummy_2640_);
v___x_2643_ = lean_unsigned_to_nat(1u);
v___x_2644_ = lean_nat_sub(v_nargs_2641_, v___x_2643_);
lean_dec(v_nargs_2641_);
v___x_2645_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2618_, v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v___y_2633_, v___x_2642_, v___x_2644_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2645_;
}
case 10:
{
lean_object* v_data_2646_; lean_object* v_expr_2647_; lean_object* v___x_2648_; 
v_data_2646_ = lean_ctor_get(v___y_2633_, 0);
v_expr_2647_ = lean_ctor_get(v___y_2633_, 1);
lean_inc_ref(v_expr_2647_);
lean_inc_ref(v_post_2615_);
lean_inc_ref(v_pre_2613_);
v___x_2648_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v_expr_2647_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; size_t v___x_2650_; size_t v___x_2651_; uint8_t v___x_2652_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___x_2648_, 1);
v___x_2650_ = lean_ptr_addr(v_expr_2647_);
v___x_2651_ = lean_ptr_addr(v_a_2649_);
v___x_2652_ = lean_usize_dec_eq(v___x_2650_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_inc(v_data_2646_);
lean_dec_ref_known(v___y_2633_, 2);
v___x_2653_ = l_Lean_Expr_mdata___override(v_data_2646_, v_a_2649_);
v___x_2654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v___x_2653_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2654_;
}
else
{
lean_object* v___x_2655_; 
lean_dec(v_a_2649_);
v___x_2655_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v___y_2633_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2655_;
}
}
else
{
lean_dec_ref_known(v___y_2633_, 2);
lean_dec_ref(v_post_2615_);
lean_dec_ref(v_pre_2613_);
return v___x_2648_;
}
}
case 11:
{
lean_object* v_typeName_2656_; lean_object* v_idx_2657_; lean_object* v_struct_2658_; lean_object* v___x_2659_; 
v_typeName_2656_ = lean_ctor_get(v___y_2633_, 0);
v_idx_2657_ = lean_ctor_get(v___y_2633_, 1);
v_struct_2658_ = lean_ctor_get(v___y_2633_, 2);
lean_inc_ref(v_struct_2658_);
lean_inc_ref(v_post_2615_);
lean_inc_ref(v_pre_2613_);
v___x_2659_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v_struct_2658_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; size_t v___x_2661_; size_t v___x_2662_; uint8_t v___x_2663_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = lean_ptr_addr(v_struct_2658_);
v___x_2662_ = lean_ptr_addr(v_a_2660_);
v___x_2663_ = lean_usize_dec_eq(v___x_2661_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_inc(v_idx_2657_);
lean_inc(v_typeName_2656_);
lean_dec_ref_known(v___y_2633_, 3);
v___x_2664_ = l_Lean_Expr_proj___override(v_typeName_2656_, v_idx_2657_, v_a_2660_);
v___x_2665_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v___x_2664_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2665_;
}
else
{
lean_object* v___x_2666_; 
lean_dec(v_a_2660_);
v___x_2666_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v___y_2633_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2666_;
}
}
else
{
lean_dec_ref_known(v___y_2633_, 3);
lean_dec_ref(v_post_2615_);
lean_dec_ref(v_pre_2613_);
return v___x_2659_;
}
}
default: 
{
lean_object* v___x_2667_; 
v___x_2667_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2613_, v_post_2615_, v_usedLetOnly_2616_, v_skipConstInApp_2617_, v_skipInstances_2618_, v___y_2633_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2667_;
}
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec_ref(v_post_2615_);
lean_dec_ref(v_e_2614_);
lean_dec_ref(v_pre_2613_);
v_a_2677_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2627_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2627_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec_ref(v_post_2615_);
lean_dec_ref(v_e_2614_);
lean_dec_ref(v_pre_2613_);
v_a_2685_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2626_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2626_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2693_, lean_object* v_pre_2694_, lean_object* v_e_2695_, lean_object* v_post_2696_, lean_object* v_usedLetOnly_2697_, lean_object* v_skipConstInApp_2698_, lean_object* v_skipInstances_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
uint8_t v_usedLetOnly_boxed_2707_; uint8_t v_skipConstInApp_boxed_2708_; uint8_t v_skipInstances_boxed_2709_; lean_object* v_res_2710_; 
v_usedLetOnly_boxed_2707_ = lean_unbox(v_usedLetOnly_2697_);
v_skipConstInApp_boxed_2708_ = lean_unbox(v_skipConstInApp_2698_);
v_skipInstances_boxed_2709_ = lean_unbox(v_skipInstances_2699_);
v_res_2710_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2693_, v_pre_2694_, v_e_2695_, v_post_2696_, v_usedLetOnly_boxed_2707_, v_skipConstInApp_boxed_2708_, v_skipInstances_boxed_2709_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec(v___y_2700_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object* v_pre_2711_, lean_object* v_post_2712_, uint8_t v_usedLetOnly_2713_, uint8_t v_skipConstInApp_2714_, uint8_t v_skipInstances_2715_, lean_object* v_e_2716_, lean_object* v_a_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_inc(v_a_2717_);
v___x_2724_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2724_, 0, lean_box(0));
lean_closure_set(v___x_2724_, 1, lean_box(0));
lean_closure_set(v___x_2724_, 2, v_a_2717_);
v___x_2725_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_2724_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2760_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2760_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2760_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_2726_, v_e_2716_);
lean_dec(v_a_2726_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___f_2735_; lean_object* v___x_2736_; 
lean_del_object(v___x_2728_);
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0));
v___x_2732_ = lean_box(v_usedLetOnly_2713_);
v___x_2733_ = lean_box(v_skipConstInApp_2714_);
v___x_2734_ = lean_box(v_skipInstances_2715_);
lean_inc_ref(v_e_2716_);
v___f_2735_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed), 14, 7);
lean_closure_set(v___f_2735_, 0, v___x_2731_);
lean_closure_set(v___f_2735_, 1, v_pre_2711_);
lean_closure_set(v___f_2735_, 2, v_e_2716_);
lean_closure_set(v___f_2735_, 3, v_post_2712_);
lean_closure_set(v___f_2735_, 4, v___x_2732_);
lean_closure_set(v___f_2735_, 5, v___x_2733_);
lean_closure_set(v___f_2735_, 6, v___x_2734_);
v___x_2736_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_2735_, v_a_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___f_2738_; lean_object* v___x_2739_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc_n(v_a_2737_, 2);
lean_dec_ref_known(v___x_2736_, 1);
lean_inc(v_a_2717_);
v___f_2738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2738_, 0, v_a_2717_);
lean_closure_set(v___f_2738_, 1, v_e_2716_);
lean_closure_set(v___f_2738_, 2, v_a_2737_);
v___x_2739_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_2738_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2746_ == 0)
{
lean_object* v_unused_2747_; 
v_unused_2747_ = lean_ctor_get(v___x_2739_, 0);
lean_dec(v_unused_2747_);
v___x_2741_ = v___x_2739_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_dec(v___x_2739_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v_a_2737_);
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2737_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v_a_2737_);
v_a_2748_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2739_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2739_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
else
{
lean_dec_ref(v_e_2716_);
return v___x_2736_;
}
}
else
{
lean_object* v_val_2756_; lean_object* v___x_2758_; 
lean_dec_ref(v_e_2716_);
lean_dec_ref(v_post_2712_);
lean_dec_ref(v_pre_2711_);
v_val_2756_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_val_2756_);
lean_dec_ref_known(v___x_2730_, 1);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v_val_2756_);
v___x_2758_ = v___x_2728_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_val_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec_ref(v_e_2716_);
lean_dec_ref(v_post_2712_);
lean_dec_ref(v_pre_2711_);
v_a_2761_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2725_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2725_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2769_, lean_object* v_pre_2770_, lean_object* v_post_2771_, lean_object* v_usedLetOnly_2772_, lean_object* v_skipConstInApp_2773_, lean_object* v_skipInstances_2774_, lean_object* v_body_2775_, lean_object* v_x_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
uint8_t v_usedLetOnly_boxed_2784_; uint8_t v_skipConstInApp_boxed_2785_; uint8_t v_skipInstances_boxed_2786_; lean_object* v_res_2787_; 
v_usedLetOnly_boxed_2784_ = lean_unbox(v_usedLetOnly_2772_);
v_skipConstInApp_boxed_2785_ = lean_unbox(v_skipConstInApp_2773_);
v_skipInstances_boxed_2786_ = lean_unbox(v_skipInstances_2774_);
v_res_2787_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2769_, v_pre_2770_, v_post_2771_, v_usedLetOnly_boxed_2784_, v_skipConstInApp_boxed_2785_, v_skipInstances_boxed_2786_, v_body_2775_, v_x_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2788_, lean_object* v_post_2789_, uint8_t v_usedLetOnly_2790_, uint8_t v_skipConstInApp_2791_, uint8_t v_skipInstances_2792_, lean_object* v_fvars_2793_, lean_object* v_e_2794_, lean_object* v_a_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
if (lean_obj_tag(v_e_2794_) == 7)
{
lean_object* v_binderName_2802_; lean_object* v_binderType_2803_; lean_object* v_body_2804_; uint8_t v_binderInfo_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_binderName_2802_ = lean_ctor_get(v_e_2794_, 0);
lean_inc(v_binderName_2802_);
v_binderType_2803_ = lean_ctor_get(v_e_2794_, 1);
lean_inc_ref(v_binderType_2803_);
v_body_2804_ = lean_ctor_get(v_e_2794_, 2);
lean_inc_ref(v_body_2804_);
v_binderInfo_2805_ = lean_ctor_get_uint8(v_e_2794_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2794_, 3);
v___x_2806_ = lean_expr_instantiate_rev(v_binderType_2803_, v_fvars_2793_);
lean_dec_ref(v_binderType_2803_);
lean_inc_ref(v_post_2789_);
lean_inc_ref(v_pre_2788_);
v___x_2807_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2788_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v___x_2806_, v_a_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___f_2812_; uint8_t v___x_2813_; lean_object* v___x_2814_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = lean_box(v_usedLetOnly_2790_);
v___x_2810_ = lean_box(v_skipConstInApp_2791_);
v___x_2811_ = lean_box(v_skipInstances_2792_);
v___f_2812_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2812_, 0, v_fvars_2793_);
lean_closure_set(v___f_2812_, 1, v_pre_2788_);
lean_closure_set(v___f_2812_, 2, v_post_2789_);
lean_closure_set(v___f_2812_, 3, v___x_2809_);
lean_closure_set(v___f_2812_, 4, v___x_2810_);
lean_closure_set(v___f_2812_, 5, v___x_2811_);
lean_closure_set(v___f_2812_, 6, v_body_2804_);
v___x_2813_ = 0;
v___x_2814_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2802_, v_binderInfo_2805_, v_a_2808_, v___f_2812_, v___x_2813_, v_a_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
return v___x_2814_;
}
else
{
lean_dec_ref(v_body_2804_);
lean_dec(v_binderName_2802_);
lean_dec_ref(v_fvars_2793_);
lean_dec_ref(v_post_2789_);
lean_dec_ref(v_pre_2788_);
return v___x_2807_;
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = lean_expr_instantiate_rev(v_e_2794_, v_fvars_2793_);
lean_dec_ref(v_e_2794_);
lean_inc_ref(v_post_2789_);
lean_inc_ref(v_pre_2788_);
v___x_2816_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2788_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v___x_2815_, v_a_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; uint8_t v___x_2818_; uint8_t v___x_2819_; uint8_t v___x_2820_; lean_object* v___x_2821_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
v___x_2818_ = 0;
v___x_2819_ = 1;
v___x_2820_ = 1;
v___x_2821_ = l_Lean_Meta_mkForallFVars(v_fvars_2793_, v_a_2817_, v___x_2818_, v_usedLetOnly_2790_, v___x_2819_, v___x_2820_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec_ref(v_fvars_2793_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2823_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___x_2823_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2788_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v_a_2822_, v_a_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
return v___x_2823_;
}
else
{
lean_dec_ref(v_post_2789_);
lean_dec_ref(v_pre_2788_);
return v___x_2821_;
}
}
else
{
lean_dec_ref(v_fvars_2793_);
lean_dec_ref(v_post_2789_);
lean_dec_ref(v_pre_2788_);
return v___x_2816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2824_, lean_object* v_pre_2825_, lean_object* v_post_2826_, uint8_t v_usedLetOnly_2827_, uint8_t v_skipConstInApp_2828_, uint8_t v_skipInstances_2829_, lean_object* v_body_2830_, lean_object* v_x_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_array_push(v_fvars_2824_, v_x_2831_);
v___x_2840_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2825_, v_post_2826_, v_usedLetOnly_2827_, v_skipConstInApp_2828_, v_skipInstances_2829_, v___x_2839_, v_body_2830_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2841_, lean_object* v_post_2842_, lean_object* v_usedLetOnly_2843_, lean_object* v_skipConstInApp_2844_, lean_object* v_skipInstances_2845_, lean_object* v_e_2846_, lean_object* v_a_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
uint8_t v_usedLetOnly_boxed_2854_; uint8_t v_skipConstInApp_boxed_2855_; uint8_t v_skipInstances_boxed_2856_; lean_object* v_res_2857_; 
v_usedLetOnly_boxed_2854_ = lean_unbox(v_usedLetOnly_2843_);
v_skipConstInApp_boxed_2855_ = lean_unbox(v_skipConstInApp_2844_);
v_skipInstances_boxed_2856_ = lean_unbox(v_skipInstances_2845_);
v_res_2857_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2841_, v_post_2842_, v_usedLetOnly_boxed_2854_, v_skipConstInApp_boxed_2855_, v_skipInstances_boxed_2856_, v_e_2846_, v_a_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v_a_2847_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2858_, lean_object* v_post_2859_, lean_object* v_usedLetOnly_2860_, lean_object* v_skipConstInApp_2861_, lean_object* v_skipInstances_2862_, lean_object* v_sz_2863_, lean_object* v_i_2864_, lean_object* v_bs_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
uint8_t v_usedLetOnly_boxed_2873_; uint8_t v_skipConstInApp_boxed_2874_; uint8_t v_skipInstances_boxed_2875_; size_t v_sz_boxed_2876_; size_t v_i_boxed_2877_; lean_object* v_res_2878_; 
v_usedLetOnly_boxed_2873_ = lean_unbox(v_usedLetOnly_2860_);
v_skipConstInApp_boxed_2874_ = lean_unbox(v_skipConstInApp_2861_);
v_skipInstances_boxed_2875_ = lean_unbox(v_skipInstances_2862_);
v_sz_boxed_2876_ = lean_unbox_usize(v_sz_2863_);
lean_dec(v_sz_2863_);
v_i_boxed_2877_ = lean_unbox_usize(v_i_2864_);
lean_dec(v_i_2864_);
v_res_2878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2858_, v_post_2859_, v_usedLetOnly_boxed_2873_, v_skipConstInApp_boxed_2874_, v_skipInstances_boxed_2875_, v_sz_boxed_2876_, v_i_boxed_2877_, v_bs_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec(v___y_2866_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_2879_, lean_object* v_post_2880_, lean_object* v_usedLetOnly_2881_, lean_object* v_skipConstInApp_2882_, lean_object* v_skipInstances_2883_, lean_object* v_e_2884_, lean_object* v_a_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
uint8_t v_usedLetOnly_boxed_2892_; uint8_t v_skipConstInApp_boxed_2893_; uint8_t v_skipInstances_boxed_2894_; lean_object* v_res_2895_; 
v_usedLetOnly_boxed_2892_ = lean_unbox(v_usedLetOnly_2881_);
v_skipConstInApp_boxed_2893_ = lean_unbox(v_skipConstInApp_2882_);
v_skipInstances_boxed_2894_ = lean_unbox(v_skipInstances_2883_);
v_res_2895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2879_, v_post_2880_, v_usedLetOnly_boxed_2892_, v_skipConstInApp_boxed_2893_, v_skipInstances_boxed_2894_, v_e_2884_, v_a_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v_a_2885_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_2896_, lean_object* v_post_2897_, lean_object* v_usedLetOnly_2898_, lean_object* v_skipConstInApp_2899_, lean_object* v_skipInstances_2900_, lean_object* v_fvars_2901_, lean_object* v_e_2902_, lean_object* v_a_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
uint8_t v_usedLetOnly_boxed_2910_; uint8_t v_skipConstInApp_boxed_2911_; uint8_t v_skipInstances_boxed_2912_; lean_object* v_res_2913_; 
v_usedLetOnly_boxed_2910_ = lean_unbox(v_usedLetOnly_2898_);
v_skipConstInApp_boxed_2911_ = lean_unbox(v_skipConstInApp_2899_);
v_skipInstances_boxed_2912_ = lean_unbox(v_skipInstances_2900_);
v_res_2913_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2896_, v_post_2897_, v_usedLetOnly_boxed_2910_, v_skipConstInApp_boxed_2911_, v_skipInstances_boxed_2912_, v_fvars_2901_, v_e_2902_, v_a_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec(v_a_2903_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_2914_, lean_object* v_post_2915_, lean_object* v_usedLetOnly_2916_, lean_object* v_skipConstInApp_2917_, lean_object* v_skipInstances_2918_, lean_object* v_fvars_2919_, lean_object* v_e_2920_, lean_object* v_a_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v_usedLetOnly_boxed_2928_; uint8_t v_skipConstInApp_boxed_2929_; uint8_t v_skipInstances_boxed_2930_; lean_object* v_res_2931_; 
v_usedLetOnly_boxed_2928_ = lean_unbox(v_usedLetOnly_2916_);
v_skipConstInApp_boxed_2929_ = lean_unbox(v_skipConstInApp_2917_);
v_skipInstances_boxed_2930_ = lean_unbox(v_skipInstances_2918_);
v_res_2931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2914_, v_post_2915_, v_usedLetOnly_boxed_2928_, v_skipConstInApp_boxed_2929_, v_skipInstances_boxed_2930_, v_fvars_2919_, v_e_2920_, v_a_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec(v_a_2921_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_2932_, lean_object* v_post_2933_, lean_object* v_usedLetOnly_2934_, lean_object* v_skipConstInApp_2935_, lean_object* v_skipInstances_2936_, lean_object* v_fvars_2937_, lean_object* v_e_2938_, lean_object* v_a_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
uint8_t v_usedLetOnly_boxed_2946_; uint8_t v_skipConstInApp_boxed_2947_; uint8_t v_skipInstances_boxed_2948_; lean_object* v_res_2949_; 
v_usedLetOnly_boxed_2946_ = lean_unbox(v_usedLetOnly_2934_);
v_skipConstInApp_boxed_2947_ = lean_unbox(v_skipConstInApp_2935_);
v_skipInstances_boxed_2948_ = lean_unbox(v_skipInstances_2936_);
v_res_2949_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2932_, v_post_2933_, v_usedLetOnly_boxed_2946_, v_skipConstInApp_boxed_2947_, v_skipInstances_boxed_2948_, v_fvars_2937_, v_e_2938_, v_a_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec(v_a_2939_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_2950_, lean_object* v___x_2951_, lean_object* v_pre_2952_, lean_object* v_post_2953_, lean_object* v_usedLetOnly_2954_, lean_object* v_skipConstInApp_2955_, lean_object* v_skipInstances_2956_, lean_object* v_a_2957_, lean_object* v_b_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
uint8_t v_usedLetOnly_boxed_2966_; uint8_t v_skipConstInApp_boxed_2967_; uint8_t v_skipInstances_boxed_2968_; lean_object* v_res_2969_; 
v_usedLetOnly_boxed_2966_ = lean_unbox(v_usedLetOnly_2954_);
v_skipConstInApp_boxed_2967_ = lean_unbox(v_skipConstInApp_2955_);
v_skipInstances_boxed_2968_ = lean_unbox(v_skipInstances_2956_);
v_res_2969_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_2950_, v___x_2951_, v_pre_2952_, v_post_2953_, v_usedLetOnly_boxed_2966_, v_skipConstInApp_boxed_2967_, v_skipInstances_boxed_2968_, v_a_2957_, v_b_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___x_2951_);
lean_dec(v_upperBound_2950_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_2970_, lean_object* v_pre_2971_, lean_object* v_post_2972_, lean_object* v_usedLetOnly_2973_, lean_object* v_skipConstInApp_2974_, lean_object* v_x_2975_, lean_object* v_x_2976_, lean_object* v_x_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
uint8_t v_skipInstances_boxed_2985_; uint8_t v_usedLetOnly_boxed_2986_; uint8_t v_skipConstInApp_boxed_2987_; lean_object* v_res_2988_; 
v_skipInstances_boxed_2985_ = lean_unbox(v_skipInstances_2970_);
v_usedLetOnly_boxed_2986_ = lean_unbox(v_usedLetOnly_2973_);
v_skipConstInApp_boxed_2987_ = lean_unbox(v_skipConstInApp_2974_);
v_res_2988_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_2985_, v_pre_2971_, v_post_2972_, v_usedLetOnly_boxed_2986_, v_skipConstInApp_boxed_2987_, v_x_2975_, v_x_2976_, v_x_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec(v___y_2978_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_2989_, lean_object* v_x_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = lean_apply_1(v_x_2990_, lean_box(0));
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2999_, lean_object* v_x_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_2999_, v_x_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
return v_res_3007_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = lean_box(0);
v___x_3009_ = lean_unsigned_to_nat(16u);
v___x_3010_ = lean_mk_array(v___x_3009_, v___x_3008_);
return v___x_3010_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
v___x_3012_ = lean_unsigned_to_nat(0u);
v___x_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v___x_3011_);
return v___x_3013_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3015_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3015_, 0, lean_box(0));
lean_closure_set(v___x_3015_, 1, lean_box(0));
lean_closure_set(v___x_3015_, 2, v___x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3016_, lean_object* v_pre_3017_, lean_object* v_post_3018_, uint8_t v_usedLetOnly_3019_, uint8_t v_skipConstInApp_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_a_3029_; uint8_t v___x_3030_; lean_object* v___x_3031_; 
v___x_3027_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3028_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3027_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref(v___x_3028_);
v___x_3030_ = 0;
v___x_3031_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3017_, v_post_3018_, v_usedLetOnly_3019_, v_skipConstInApp_3020_, v___x_3030_, v_input_3016_, v_a_3029_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3031_, 1);
v___x_3033_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3033_, 0, lean_box(0));
lean_closure_set(v___x_3033_, 1, lean_box(0));
lean_closure_set(v___x_3033_, 2, v_a_3029_);
v___x_3034_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3033_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v___x_3034_, 0);
lean_dec(v_unused_3042_);
v___x_3036_ = v___x_3034_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_dec(v___x_3034_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v_a_3032_);
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3032_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
else
{
lean_dec(v_a_3029_);
return v___x_3031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3043_, lean_object* v_pre_3044_, lean_object* v_post_3045_, lean_object* v_usedLetOnly_3046_, lean_object* v_skipConstInApp_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
uint8_t v_usedLetOnly_boxed_3054_; uint8_t v_skipConstInApp_boxed_3055_; lean_object* v_res_3056_; 
v_usedLetOnly_boxed_3054_ = lean_unbox(v_usedLetOnly_3046_);
v_skipConstInApp_boxed_3055_ = lean_unbox(v_skipConstInApp_3047_);
v_res_3056_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3043_, v_pre_3044_, v_post_3045_, v_usedLetOnly_boxed_3054_, v_skipConstInApp_boxed_3055_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3058_, uint8_t v_elimTrivial_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v_pre_3068_; lean_object* v___f_3069_; uint8_t v___x_3070_; lean_object* v___x_3071_; 
v___x_3065_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_3066_ = lean_st_mk_ref(v___x_3065_);
v___x_3067_ = lean_box(v_elimTrivial_3059_);
v_pre_3068_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3068_, 0, v___x_3067_);
v___f_3069_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0));
v___x_3070_ = 0;
v___x_3071_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3058_, v_pre_3068_, v___f_3069_, v___x_3070_, v___x_3070_, v___x_3066_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3080_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3074_ = v___x_3071_;
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3071_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = lean_st_ref_get(v___x_3066_);
lean_dec(v___x_3066_);
lean_dec(v___x_3076_);
if (v_isShared_3075_ == 0)
{
v___x_3078_ = v___x_3074_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3072_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
else
{
lean_dec(v___x_3066_);
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3081_, lean_object* v_elimTrivial_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_){
_start:
{
uint8_t v_elimTrivial_boxed_3088_; lean_object* v_res_3089_; 
v_elimTrivial_boxed_3088_ = lean_unbox(v_elimTrivial_3082_);
v_res_3089_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3081_, v_elimTrivial_boxed_3088_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_upperBound_3090_, lean_object* v___x_3091_, lean_object* v_pre_3092_, lean_object* v_post_3093_, uint8_t v_usedLetOnly_3094_, uint8_t v_skipConstInApp_3095_, uint8_t v_skipInstances_3096_, lean_object* v___x_3097_, lean_object* v_inst_3098_, lean_object* v_R_3099_, lean_object* v_a_3100_, lean_object* v_b_3101_, lean_object* v_c_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3090_, v___x_3091_, v_pre_3092_, v_post_3093_, v_usedLetOnly_3094_, v_skipConstInApp_3095_, v_skipInstances_3096_, v_a_3100_, v_b_3101_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3111_ = _args[0];
lean_object* v___x_3112_ = _args[1];
lean_object* v_pre_3113_ = _args[2];
lean_object* v_post_3114_ = _args[3];
lean_object* v_usedLetOnly_3115_ = _args[4];
lean_object* v_skipConstInApp_3116_ = _args[5];
lean_object* v_skipInstances_3117_ = _args[6];
lean_object* v___x_3118_ = _args[7];
lean_object* v_inst_3119_ = _args[8];
lean_object* v_R_3120_ = _args[9];
lean_object* v_a_3121_ = _args[10];
lean_object* v_b_3122_ = _args[11];
lean_object* v_c_3123_ = _args[12];
lean_object* v___y_3124_ = _args[13];
lean_object* v___y_3125_ = _args[14];
lean_object* v___y_3126_ = _args[15];
lean_object* v___y_3127_ = _args[16];
lean_object* v___y_3128_ = _args[17];
lean_object* v___y_3129_ = _args[18];
lean_object* v___y_3130_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3131_; uint8_t v_skipConstInApp_boxed_3132_; uint8_t v_skipInstances_boxed_3133_; lean_object* v_res_3134_; 
v_usedLetOnly_boxed_3131_ = lean_unbox(v_usedLetOnly_3115_);
v_skipConstInApp_boxed_3132_ = lean_unbox(v_skipConstInApp_3116_);
v_skipInstances_boxed_3133_ = lean_unbox(v_skipInstances_3117_);
v_res_3134_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3111_, v___x_3112_, v_pre_3113_, v_post_3114_, v_usedLetOnly_boxed_3131_, v_skipConstInApp_boxed_3132_, v_skipInstances_boxed_3133_, v___x_3118_, v_inst_3119_, v_R_3120_, v_a_3121_, v_b_3122_, v_c_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec(v___x_3118_);
lean_dec_ref(v___x_3112_);
lean_dec(v_upperBound_3111_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3135_, lean_object* v_m_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_3136_, v_a_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_3139_, lean_object* v_m_3140_, lean_object* v_a_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_3139_, v_m_3140_, v_a_3141_);
lean_dec_ref(v_a_3141_);
lean_dec_ref(v_m_3140_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3143_, lean_object* v_name_3144_, uint8_t v_bi_3145_, lean_object* v_type_3146_, lean_object* v_k_3147_, uint8_t v_kind_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3144_, v_bi_3145_, v_type_3146_, v_k_3147_, v_kind_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3157_, lean_object* v_name_3158_, lean_object* v_bi_3159_, lean_object* v_type_3160_, lean_object* v_k_3161_, lean_object* v_kind_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
uint8_t v_bi_boxed_3170_; uint8_t v_kind_boxed_3171_; lean_object* v_res_3172_; 
v_bi_boxed_3170_ = lean_unbox(v_bi_3159_);
v_kind_boxed_3171_ = lean_unbox(v_kind_3162_);
v_res_3172_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3157_, v_name_3158_, v_bi_boxed_3170_, v_type_3160_, v_k_3161_, v_kind_boxed_3171_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec(v___y_3163_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3173_, lean_object* v_name_3174_, lean_object* v_type_3175_, lean_object* v_val_3176_, lean_object* v_k_3177_, uint8_t v_nondep_3178_, uint8_t v_kind_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3174_, v_type_3175_, v_val_3176_, v_k_3177_, v_nondep_3178_, v_kind_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3188_, lean_object* v_name_3189_, lean_object* v_type_3190_, lean_object* v_val_3191_, lean_object* v_k_3192_, lean_object* v_nondep_3193_, lean_object* v_kind_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
uint8_t v_nondep_boxed_3202_; uint8_t v_kind_boxed_3203_; lean_object* v_res_3204_; 
v_nondep_boxed_3202_ = lean_unbox(v_nondep_3193_);
v_kind_boxed_3203_ = lean_unbox(v_kind_3194_);
v_res_3204_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3188_, v_name_3189_, v_type_3190_, v_val_3191_, v_k_3192_, v_nondep_boxed_3202_, v_kind_boxed_3203_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec(v___y_3195_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3205_, lean_object* v_ref_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3206_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3213_, lean_object* v_ref_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3213_, v_ref_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3221_, lean_object* v_x_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3231_, lean_object* v_x_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3231_, v_x_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec(v___y_3233_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3241_, lean_object* v_m_3242_, lean_object* v_a_3243_, lean_object* v_b_3244_){
_start:
{
lean_object* v___x_3245_; 
v___x_3245_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3242_, v_a_3243_, v_b_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_3246_, lean_object* v_a_3247_, lean_object* v_x_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_3247_, v_x_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3250_, lean_object* v_a_3251_, lean_object* v_x_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_3250_, v_a_3251_, v_x_3252_);
lean_dec(v_x_3252_);
lean_dec_ref(v_a_3251_);
return v_res_3253_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3254_, lean_object* v_a_3255_, lean_object* v_x_3256_){
_start:
{
uint8_t v___x_3257_; 
v___x_3257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_3255_, v_x_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3258_, lean_object* v_a_3259_, lean_object* v_x_3260_){
_start:
{
uint8_t v_res_3261_; lean_object* v_r_3262_; 
v_res_3261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3258_, v_a_3259_, v_x_3260_);
lean_dec(v_x_3260_);
lean_dec_ref(v_a_3259_);
v_r_3262_ = lean_box(v_res_3261_);
return v_r_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_3263_, lean_object* v_data_3264_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_3266_, lean_object* v_a_3267_, lean_object* v_b_3268_, lean_object* v_x_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_3267_, v_b_3268_, v_x_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_3271_, lean_object* v_i_3272_, lean_object* v_source_3273_, lean_object* v_target_3274_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_3272_, v_source_3273_, v_target_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_3276_, lean_object* v_x_3277_, lean_object* v_x_3278_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3277_, v_x_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3280_, lean_object* v_x_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3280_, v_x_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
v_a_3296_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3287_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3287_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3304_, lean_object* v_x_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3304_, v_x_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3312_, lean_object* v_mvarId_3313_, lean_object* v_x_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3313_, v_x_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3321_, lean_object* v_mvarId_3322_, lean_object* v_x_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3321_, v_mvarId_3322_, v_x_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3330_, lean_object* v_as_3331_, size_t v_sz_3332_, size_t v_i_3333_, lean_object* v_b_3334_){
_start:
{
uint8_t v___x_3336_; 
v___x_3336_ = lean_usize_dec_lt(v_i_3333_, v_sz_3332_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; 
v___x_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_b_3334_);
return v___x_3337_;
}
else
{
lean_object* v_snd_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3385_; 
v_snd_3338_ = lean_ctor_get(v_b_3334_, 1);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_b_3334_);
if (v_isSharedCheck_3385_ == 0)
{
lean_object* v_unused_3386_; 
v_unused_3386_ = lean_ctor_get(v_b_3334_, 0);
lean_dec(v_unused_3386_);
v___x_3340_ = v_b_3334_;
v_isShared_3341_ = v_isSharedCheck_3385_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_snd_3338_);
lean_dec(v_b_3334_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3385_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v_a_3344_; lean_object* v_a_3351_; 
v___x_3342_ = lean_box(0);
v_a_3351_ = lean_array_uget_borrowed(v_as_3331_, v_i_3333_);
if (lean_obj_tag(v_a_3351_) == 0)
{
v_a_3344_ = v_snd_3338_;
goto v___jp_3343_;
}
else
{
lean_object* v_val_3352_; lean_object* v_fst_3353_; lean_object* v_snd_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3384_; 
v_val_3352_ = lean_ctor_get(v_a_3351_, 0);
v_fst_3353_ = lean_ctor_get(v_snd_3338_, 0);
v_snd_3354_ = lean_ctor_get(v_snd_3338_, 1);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_snd_3338_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3356_ = v_snd_3338_;
v_isShared_3357_ = v_isSharedCheck_3384_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_snd_3354_);
lean_inc(v_fst_3353_);
lean_dec(v_snd_3338_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3384_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
uint8_t v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = 0;
v___x_3359_ = l_Lean_LocalDecl_value_x3f(v_val_3352_, v___x_3358_);
if (lean_obj_tag(v___x_3359_) == 1)
{
lean_object* v_val_3360_; lean_object* v___x_3361_; 
v_val_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_val_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3361_ = l_Lean_LocalDecl_type(v_val_3352_);
if (lean_obj_tag(v___x_3361_) == 10)
{
lean_object* v_data_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; uint8_t v___x_3367_; 
v_data_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_data_3362_);
lean_dec_ref_known(v___x_3361_, 2);
v___x_3363_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3364_ = lean_unsigned_to_nat(2u);
v___x_3365_ = l_Lean_KVMap_getNat(v_data_3362_, v___x_3363_, v___x_3364_);
lean_dec(v_data_3362_);
v___x_3366_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3365_);
lean_dec(v___x_3365_);
v___x_3367_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3366_, v_val_3360_, v_elimTrivial_3330_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3373_; 
v___x_3368_ = l_Lean_LocalDecl_fvarId(v_val_3352_);
v___x_3369_ = l_Lean_mkFVar(v___x_3368_);
v___x_3370_ = lean_array_push(v_fst_3353_, v___x_3369_);
v___x_3371_ = lean_array_push(v_snd_3354_, v_val_3360_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 1, v___x_3371_);
lean_ctor_set(v___x_3356_, 0, v___x_3370_);
v___x_3373_ = v___x_3356_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
v_a_3344_ = v___x_3373_;
goto v___jp_3343_;
}
}
else
{
lean_object* v___x_3376_; 
lean_dec(v_val_3360_);
if (v_isShared_3357_ == 0)
{
v___x_3376_ = v___x_3356_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_fst_3353_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v_snd_3354_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
v_a_3344_ = v___x_3376_;
goto v___jp_3343_;
}
}
}
else
{
lean_object* v___x_3379_; 
lean_dec_ref(v___x_3361_);
lean_dec(v_val_3360_);
if (v_isShared_3357_ == 0)
{
v___x_3379_ = v___x_3356_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_fst_3353_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_snd_3354_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
v_a_3344_ = v___x_3379_;
goto v___jp_3343_;
}
}
}
else
{
lean_object* v___x_3382_; 
lean_dec(v___x_3359_);
if (v_isShared_3357_ == 0)
{
v___x_3382_ = v___x_3356_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_fst_3353_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_snd_3354_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
v_a_3344_ = v___x_3382_;
goto v___jp_3343_;
}
}
}
}
v___jp_3343_:
{
lean_object* v___x_3346_; 
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 1, v_a_3344_);
lean_ctor_set(v___x_3340_, 0, v___x_3342_);
v___x_3346_ = v___x_3340_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_a_3344_);
v___x_3346_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
size_t v___x_3347_; size_t v___x_3348_; 
v___x_3347_ = ((size_t)1ULL);
v___x_3348_ = lean_usize_add(v_i_3333_, v___x_3347_);
v_i_3333_ = v___x_3348_;
v_b_3334_ = v___x_3346_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3387_, lean_object* v_as_3388_, lean_object* v_sz_3389_, lean_object* v_i_3390_, lean_object* v_b_3391_, lean_object* v___y_3392_){
_start:
{
uint8_t v_elimTrivial_boxed_3393_; size_t v_sz_boxed_3394_; size_t v_i_boxed_3395_; lean_object* v_res_3396_; 
v_elimTrivial_boxed_3393_ = lean_unbox(v_elimTrivial_3387_);
v_sz_boxed_3394_ = lean_unbox_usize(v_sz_3389_);
lean_dec(v_sz_3389_);
v_i_boxed_3395_ = lean_unbox_usize(v_i_3390_);
lean_dec(v_i_3390_);
v_res_3396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3393_, v_as_3388_, v_sz_boxed_3394_, v_i_boxed_3395_, v_b_3391_);
lean_dec_ref(v_as_3388_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3397_, lean_object* v_as_3398_, size_t v_sz_3399_, size_t v_i_3400_, lean_object* v_b_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
uint8_t v___x_3407_; 
v___x_3407_ = lean_usize_dec_lt(v_i_3400_, v_sz_3399_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3408_, 0, v_b_3401_);
return v___x_3408_;
}
else
{
lean_object* v_snd_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3456_; 
v_snd_3409_ = lean_ctor_get(v_b_3401_, 1);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_b_3401_);
if (v_isSharedCheck_3456_ == 0)
{
lean_object* v_unused_3457_; 
v_unused_3457_ = lean_ctor_get(v_b_3401_, 0);
lean_dec(v_unused_3457_);
v___x_3411_ = v_b_3401_;
v_isShared_3412_ = v_isSharedCheck_3456_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_snd_3409_);
lean_dec(v_b_3401_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3456_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v_a_3415_; lean_object* v_a_3422_; 
v___x_3413_ = lean_box(0);
v_a_3422_ = lean_array_uget_borrowed(v_as_3398_, v_i_3400_);
if (lean_obj_tag(v_a_3422_) == 0)
{
v_a_3415_ = v_snd_3409_;
goto v___jp_3414_;
}
else
{
lean_object* v_val_3423_; lean_object* v_fst_3424_; lean_object* v_snd_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3455_; 
v_val_3423_ = lean_ctor_get(v_a_3422_, 0);
v_fst_3424_ = lean_ctor_get(v_snd_3409_, 0);
v_snd_3425_ = lean_ctor_get(v_snd_3409_, 1);
v_isSharedCheck_3455_ = !lean_is_exclusive(v_snd_3409_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3427_ = v_snd_3409_;
v_isShared_3428_ = v_isSharedCheck_3455_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_snd_3425_);
lean_inc(v_fst_3424_);
lean_dec(v_snd_3409_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3455_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
uint8_t v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = 0;
v___x_3430_ = l_Lean_LocalDecl_value_x3f(v_val_3423_, v___x_3429_);
if (lean_obj_tag(v___x_3430_) == 1)
{
lean_object* v_val_3431_; lean_object* v___x_3432_; 
v_val_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_val_3431_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3432_ = l_Lean_LocalDecl_type(v_val_3423_);
if (lean_obj_tag(v___x_3432_) == 10)
{
lean_object* v_data_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; uint8_t v___x_3438_; 
v_data_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_data_3433_);
lean_dec_ref_known(v___x_3432_, 2);
v___x_3434_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3435_ = lean_unsigned_to_nat(2u);
v___x_3436_ = l_Lean_KVMap_getNat(v_data_3433_, v___x_3434_, v___x_3435_);
lean_dec(v_data_3433_);
v___x_3437_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3436_);
lean_dec(v___x_3436_);
v___x_3438_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3437_, v_val_3431_, v_elimTrivial_3397_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3439_ = l_Lean_LocalDecl_fvarId(v_val_3423_);
v___x_3440_ = l_Lean_mkFVar(v___x_3439_);
v___x_3441_ = lean_array_push(v_fst_3424_, v___x_3440_);
v___x_3442_ = lean_array_push(v_snd_3425_, v_val_3431_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 1, v___x_3442_);
lean_ctor_set(v___x_3427_, 0, v___x_3441_);
v___x_3444_ = v___x_3427_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
v_a_3415_ = v___x_3444_;
goto v___jp_3414_;
}
}
else
{
lean_object* v___x_3447_; 
lean_dec(v_val_3431_);
if (v_isShared_3428_ == 0)
{
v___x_3447_ = v___x_3427_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_fst_3424_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_snd_3425_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
v_a_3415_ = v___x_3447_;
goto v___jp_3414_;
}
}
}
else
{
lean_object* v___x_3450_; 
lean_dec_ref(v___x_3432_);
lean_dec(v_val_3431_);
if (v_isShared_3428_ == 0)
{
v___x_3450_ = v___x_3427_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_fst_3424_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_snd_3425_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
v_a_3415_ = v___x_3450_;
goto v___jp_3414_;
}
}
}
else
{
lean_object* v___x_3453_; 
lean_dec(v___x_3430_);
if (v_isShared_3428_ == 0)
{
v___x_3453_ = v___x_3427_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_fst_3424_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_snd_3425_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
v_a_3415_ = v___x_3453_;
goto v___jp_3414_;
}
}
}
}
v___jp_3414_:
{
lean_object* v___x_3417_; 
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 1, v_a_3415_);
lean_ctor_set(v___x_3411_, 0, v___x_3413_);
v___x_3417_ = v___x_3411_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3413_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v_a_3415_);
v___x_3417_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
size_t v___x_3418_; size_t v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = ((size_t)1ULL);
v___x_3419_ = lean_usize_add(v_i_3400_, v___x_3418_);
v___x_3420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3397_, v_as_3398_, v_sz_3399_, v___x_3419_, v___x_3417_);
return v___x_3420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3458_, lean_object* v_as_3459_, lean_object* v_sz_3460_, lean_object* v_i_3461_, lean_object* v_b_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
uint8_t v_elimTrivial_boxed_3468_; size_t v_sz_boxed_3469_; size_t v_i_boxed_3470_; lean_object* v_res_3471_; 
v_elimTrivial_boxed_3468_ = lean_unbox(v_elimTrivial_3458_);
v_sz_boxed_3469_ = lean_unbox_usize(v_sz_3460_);
lean_dec(v_sz_3460_);
v_i_boxed_3470_ = lean_unbox_usize(v_i_3461_);
lean_dec(v_i_3461_);
v_res_3471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3468_, v_as_3459_, v_sz_boxed_3469_, v_i_boxed_3470_, v_b_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec_ref(v_as_3459_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3472_, lean_object* v_as_3473_, size_t v_sz_3474_, size_t v_i_3475_, lean_object* v_b_3476_){
_start:
{
uint8_t v___x_3478_; 
v___x_3478_ = lean_usize_dec_lt(v_i_3475_, v_sz_3474_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3479_, 0, v_b_3476_);
return v___x_3479_;
}
else
{
lean_object* v_snd_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3527_; 
v_snd_3480_ = lean_ctor_get(v_b_3476_, 1);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_b_3476_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; 
v_unused_3528_ = lean_ctor_get(v_b_3476_, 0);
lean_dec(v_unused_3528_);
v___x_3482_ = v_b_3476_;
v_isShared_3483_ = v_isSharedCheck_3527_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_snd_3480_);
lean_dec(v_b_3476_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3527_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3484_; lean_object* v_a_3486_; lean_object* v_a_3493_; 
v___x_3484_ = lean_box(0);
v_a_3493_ = lean_array_uget_borrowed(v_as_3473_, v_i_3475_);
if (lean_obj_tag(v_a_3493_) == 0)
{
v_a_3486_ = v_snd_3480_;
goto v___jp_3485_;
}
else
{
lean_object* v_val_3494_; lean_object* v_fst_3495_; lean_object* v_snd_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3526_; 
v_val_3494_ = lean_ctor_get(v_a_3493_, 0);
v_fst_3495_ = lean_ctor_get(v_snd_3480_, 0);
v_snd_3496_ = lean_ctor_get(v_snd_3480_, 1);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_snd_3480_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3498_ = v_snd_3480_;
v_isShared_3499_ = v_isSharedCheck_3526_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_snd_3496_);
lean_inc(v_fst_3495_);
lean_dec(v_snd_3480_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3526_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
uint8_t v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = 0;
v___x_3501_ = l_Lean_LocalDecl_value_x3f(v_val_3494_, v___x_3500_);
if (lean_obj_tag(v___x_3501_) == 1)
{
lean_object* v_val_3502_; lean_object* v___x_3503_; 
v_val_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_val_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = l_Lean_LocalDecl_type(v_val_3494_);
if (lean_obj_tag(v___x_3503_) == 10)
{
lean_object* v_data_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; uint8_t v___x_3509_; 
v_data_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_data_3504_);
lean_dec_ref_known(v___x_3503_, 2);
v___x_3505_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3506_ = lean_unsigned_to_nat(2u);
v___x_3507_ = l_Lean_KVMap_getNat(v_data_3504_, v___x_3505_, v___x_3506_);
lean_dec(v_data_3504_);
v___x_3508_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3507_);
lean_dec(v___x_3507_);
v___x_3509_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3508_, v_val_3502_, v_elimTrivial_3472_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3510_ = l_Lean_LocalDecl_fvarId(v_val_3494_);
v___x_3511_ = l_Lean_mkFVar(v___x_3510_);
v___x_3512_ = lean_array_push(v_fst_3495_, v___x_3511_);
v___x_3513_ = lean_array_push(v_snd_3496_, v_val_3502_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 1, v___x_3513_);
lean_ctor_set(v___x_3498_, 0, v___x_3512_);
v___x_3515_ = v___x_3498_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
v_a_3486_ = v___x_3515_;
goto v___jp_3485_;
}
}
else
{
lean_object* v___x_3518_; 
lean_dec(v_val_3502_);
if (v_isShared_3499_ == 0)
{
v___x_3518_ = v___x_3498_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_fst_3495_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_snd_3496_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
v_a_3486_ = v___x_3518_;
goto v___jp_3485_;
}
}
}
else
{
lean_object* v___x_3521_; 
lean_dec_ref(v___x_3503_);
lean_dec(v_val_3502_);
if (v_isShared_3499_ == 0)
{
v___x_3521_ = v___x_3498_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_fst_3495_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_snd_3496_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
v_a_3486_ = v___x_3521_;
goto v___jp_3485_;
}
}
}
else
{
lean_object* v___x_3524_; 
lean_dec(v___x_3501_);
if (v_isShared_3499_ == 0)
{
v___x_3524_ = v___x_3498_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_fst_3495_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_snd_3496_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
v_a_3486_ = v___x_3524_;
goto v___jp_3485_;
}
}
}
}
v___jp_3485_:
{
lean_object* v___x_3488_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 1, v_a_3486_);
lean_ctor_set(v___x_3482_, 0, v___x_3484_);
v___x_3488_ = v___x_3482_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_a_3486_);
v___x_3488_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
size_t v___x_3489_; size_t v___x_3490_; 
v___x_3489_ = ((size_t)1ULL);
v___x_3490_ = lean_usize_add(v_i_3475_, v___x_3489_);
v_i_3475_ = v___x_3490_;
v_b_3476_ = v___x_3488_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3529_, lean_object* v_as_3530_, lean_object* v_sz_3531_, lean_object* v_i_3532_, lean_object* v_b_3533_, lean_object* v___y_3534_){
_start:
{
uint8_t v_elimTrivial_boxed_3535_; size_t v_sz_boxed_3536_; size_t v_i_boxed_3537_; lean_object* v_res_3538_; 
v_elimTrivial_boxed_3535_ = lean_unbox(v_elimTrivial_3529_);
v_sz_boxed_3536_ = lean_unbox_usize(v_sz_3531_);
lean_dec(v_sz_3531_);
v_i_boxed_3537_ = lean_unbox_usize(v_i_3532_);
lean_dec(v_i_3532_);
v_res_3538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3535_, v_as_3530_, v_sz_boxed_3536_, v_i_boxed_3537_, v_b_3533_);
lean_dec_ref(v_as_3530_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3539_, lean_object* v_as_3540_, size_t v_sz_3541_, size_t v_i_3542_, lean_object* v_b_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
uint8_t v___x_3549_; 
v___x_3549_ = lean_usize_dec_lt(v_i_3542_, v_sz_3541_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_b_3543_);
return v___x_3550_;
}
else
{
lean_object* v_snd_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3598_; 
v_snd_3551_ = lean_ctor_get(v_b_3543_, 1);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_b_3543_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; 
v_unused_3599_ = lean_ctor_get(v_b_3543_, 0);
lean_dec(v_unused_3599_);
v___x_3553_ = v_b_3543_;
v_isShared_3554_ = v_isSharedCheck_3598_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_snd_3551_);
lean_dec(v_b_3543_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3598_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; lean_object* v_a_3557_; lean_object* v_a_3564_; 
v___x_3555_ = lean_box(0);
v_a_3564_ = lean_array_uget_borrowed(v_as_3540_, v_i_3542_);
if (lean_obj_tag(v_a_3564_) == 0)
{
v_a_3557_ = v_snd_3551_;
goto v___jp_3556_;
}
else
{
lean_object* v_val_3565_; lean_object* v_fst_3566_; lean_object* v_snd_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3597_; 
v_val_3565_ = lean_ctor_get(v_a_3564_, 0);
v_fst_3566_ = lean_ctor_get(v_snd_3551_, 0);
v_snd_3567_ = lean_ctor_get(v_snd_3551_, 1);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_snd_3551_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3569_ = v_snd_3551_;
v_isShared_3570_ = v_isSharedCheck_3597_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_snd_3567_);
lean_inc(v_fst_3566_);
lean_dec(v_snd_3551_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3597_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
uint8_t v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = 0;
v___x_3572_ = l_Lean_LocalDecl_value_x3f(v_val_3565_, v___x_3571_);
if (lean_obj_tag(v___x_3572_) == 1)
{
lean_object* v_val_3573_; lean_object* v___x_3574_; 
v_val_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_val_3573_);
lean_dec_ref_known(v___x_3572_, 1);
v___x_3574_ = l_Lean_LocalDecl_type(v_val_3565_);
if (lean_obj_tag(v___x_3574_) == 10)
{
lean_object* v_data_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; uint8_t v___x_3580_; 
v_data_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_data_3575_);
lean_dec_ref_known(v___x_3574_, 2);
v___x_3576_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3577_ = lean_unsigned_to_nat(2u);
v___x_3578_ = l_Lean_KVMap_getNat(v_data_3575_, v___x_3576_, v___x_3577_);
lean_dec(v_data_3575_);
v___x_3579_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3578_);
lean_dec(v___x_3578_);
v___x_3580_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3579_, v_val_3573_, v_elimTrivial_3539_);
if (v___x_3580_ == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3581_ = l_Lean_LocalDecl_fvarId(v_val_3565_);
v___x_3582_ = l_Lean_mkFVar(v___x_3581_);
v___x_3583_ = lean_array_push(v_fst_3566_, v___x_3582_);
v___x_3584_ = lean_array_push(v_snd_3567_, v_val_3573_);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v___x_3584_);
lean_ctor_set(v___x_3569_, 0, v___x_3583_);
v___x_3586_ = v___x_3569_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3583_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
v_a_3557_ = v___x_3586_;
goto v___jp_3556_;
}
}
else
{
lean_object* v___x_3589_; 
lean_dec(v_val_3573_);
if (v_isShared_3570_ == 0)
{
v___x_3589_ = v___x_3569_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_fst_3566_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_snd_3567_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
v_a_3557_ = v___x_3589_;
goto v___jp_3556_;
}
}
}
else
{
lean_object* v___x_3592_; 
lean_dec_ref(v___x_3574_);
lean_dec(v_val_3573_);
if (v_isShared_3570_ == 0)
{
v___x_3592_ = v___x_3569_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_fst_3566_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_snd_3567_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
v_a_3557_ = v___x_3592_;
goto v___jp_3556_;
}
}
}
else
{
lean_object* v___x_3595_; 
lean_dec(v___x_3572_);
if (v_isShared_3570_ == 0)
{
v___x_3595_ = v___x_3569_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_fst_3566_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_snd_3567_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
v_a_3557_ = v___x_3595_;
goto v___jp_3556_;
}
}
}
}
v___jp_3556_:
{
lean_object* v___x_3559_; 
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 1, v_a_3557_);
lean_ctor_set(v___x_3553_, 0, v___x_3555_);
v___x_3559_ = v___x_3553_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_a_3557_);
v___x_3559_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
size_t v___x_3560_; size_t v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = ((size_t)1ULL);
v___x_3561_ = lean_usize_add(v_i_3542_, v___x_3560_);
v___x_3562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3539_, v_as_3540_, v_sz_3541_, v___x_3561_, v___x_3559_);
return v___x_3562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3600_, lean_object* v_as_3601_, lean_object* v_sz_3602_, lean_object* v_i_3603_, lean_object* v_b_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
uint8_t v_elimTrivial_boxed_3610_; size_t v_sz_boxed_3611_; size_t v_i_boxed_3612_; lean_object* v_res_3613_; 
v_elimTrivial_boxed_3610_ = lean_unbox(v_elimTrivial_3600_);
v_sz_boxed_3611_ = lean_unbox_usize(v_sz_3602_);
lean_dec(v_sz_3602_);
v_i_boxed_3612_ = lean_unbox_usize(v_i_3603_);
lean_dec(v_i_3603_);
v_res_3613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3610_, v_as_3601_, v_sz_boxed_3611_, v_i_boxed_3612_, v_b_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v_as_3601_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3614_, uint8_t v_elimTrivial_3615_, lean_object* v_n_3616_, lean_object* v_b_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
if (lean_obj_tag(v_n_3616_) == 0)
{
lean_object* v_cs_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; size_t v_sz_3626_; size_t v___x_3627_; lean_object* v___x_3628_; 
v_cs_3623_ = lean_ctor_get(v_n_3616_, 0);
v___x_3624_ = lean_box(0);
v___x_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
lean_ctor_set(v___x_3625_, 1, v_b_3617_);
v_sz_3626_ = lean_array_size(v_cs_3623_);
v___x_3627_ = ((size_t)0ULL);
v___x_3628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3614_, v_elimTrivial_3615_, v_cs_3623_, v_sz_3626_, v___x_3627_, v___x_3625_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3643_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3631_ = v___x_3628_;
v_isShared_3632_ = v_isSharedCheck_3643_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3628_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3643_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v_fst_3633_; 
v_fst_3633_ = lean_ctor_get(v_a_3629_, 0);
if (lean_obj_tag(v_fst_3633_) == 0)
{
lean_object* v_snd_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
v_snd_3634_ = lean_ctor_get(v_a_3629_, 1);
lean_inc(v_snd_3634_);
lean_dec(v_a_3629_);
v___x_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3635_, 0, v_snd_3634_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v___x_3635_);
v___x_3637_ = v___x_3631_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
else
{
lean_object* v_val_3639_; lean_object* v___x_3641_; 
lean_inc_ref(v_fst_3633_);
lean_dec(v_a_3629_);
v_val_3639_ = lean_ctor_get(v_fst_3633_, 0);
lean_inc(v_val_3639_);
lean_dec_ref_known(v_fst_3633_, 1);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v_val_3639_);
v___x_3641_ = v___x_3631_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_val_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
v_a_3644_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3628_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3628_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
else
{
lean_object* v_vs_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; size_t v_sz_3655_; size_t v___x_3656_; lean_object* v___x_3657_; 
v_vs_3652_ = lean_ctor_get(v_n_3616_, 0);
v___x_3653_ = lean_box(0);
v___x_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
lean_ctor_set(v___x_3654_, 1, v_b_3617_);
v_sz_3655_ = lean_array_size(v_vs_3652_);
v___x_3656_ = ((size_t)0ULL);
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3615_, v_vs_3652_, v_sz_3655_, v___x_3656_, v___x_3654_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3672_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3660_ = v___x_3657_;
v_isShared_3661_ = v_isSharedCheck_3672_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3657_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3672_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v_fst_3662_; 
v_fst_3662_ = lean_ctor_get(v_a_3658_, 0);
if (lean_obj_tag(v_fst_3662_) == 0)
{
lean_object* v_snd_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
v_snd_3663_ = lean_ctor_get(v_a_3658_, 1);
lean_inc(v_snd_3663_);
lean_dec(v_a_3658_);
v___x_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3664_, 0, v_snd_3663_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3664_);
v___x_3666_ = v___x_3660_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
else
{
lean_object* v_val_3668_; lean_object* v___x_3670_; 
lean_inc_ref(v_fst_3662_);
lean_dec(v_a_3658_);
v_val_3668_ = lean_ctor_get(v_fst_3662_, 0);
lean_inc(v_val_3668_);
lean_dec_ref_known(v_fst_3662_, 1);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v_val_3668_);
v___x_3670_ = v___x_3660_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_val_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3680_; 
v_a_3673_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3675_ = v___x_3657_;
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3657_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3680_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3681_, uint8_t v_elimTrivial_3682_, lean_object* v_as_3683_, size_t v_sz_3684_, size_t v_i_3685_, lean_object* v_b_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
uint8_t v___x_3692_; 
v___x_3692_ = lean_usize_dec_lt(v_i_3685_, v_sz_3684_);
if (v___x_3692_ == 0)
{
lean_object* v___x_3693_; 
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v_b_3686_);
return v___x_3693_;
}
else
{
lean_object* v_snd_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3728_; 
v_snd_3694_ = lean_ctor_get(v_b_3686_, 1);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_b_3686_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; 
v_unused_3729_ = lean_ctor_get(v_b_3686_, 0);
lean_dec(v_unused_3729_);
v___x_3696_ = v_b_3686_;
v_isShared_3697_ = v_isSharedCheck_3728_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_snd_3694_);
lean_dec(v_b_3686_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3728_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v_a_3698_; lean_object* v___x_3699_; 
v_a_3698_ = lean_array_uget_borrowed(v_as_3683_, v_i_3685_);
lean_inc(v_snd_3694_);
v___x_3699_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3681_, v_elimTrivial_3682_, v_a_3698_, v_snd_3694_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3719_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3702_ = v___x_3699_;
v_isShared_3703_ = v_isSharedCheck_3719_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3699_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3719_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
if (lean_obj_tag(v_a_3700_) == 0)
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3704_, 0, v_a_3700_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 0, v___x_3704_);
v___x_3706_ = v___x_3696_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_snd_3694_);
v___x_3706_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3708_; 
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v___x_3706_);
v___x_3708_ = v___x_3702_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3712_; lean_object* v___x_3714_; 
lean_del_object(v___x_3702_);
lean_dec(v_snd_3694_);
v_a_3711_ = lean_ctor_get(v_a_3700_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v_a_3700_, 1);
v___x_3712_ = lean_box(0);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 1, v_a_3711_);
lean_ctor_set(v___x_3696_, 0, v___x_3712_);
v___x_3714_ = v___x_3696_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_a_3711_);
v___x_3714_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
size_t v___x_3715_; size_t v___x_3716_; 
v___x_3715_ = ((size_t)1ULL);
v___x_3716_ = lean_usize_add(v_i_3685_, v___x_3715_);
v_i_3685_ = v___x_3716_;
v_b_3686_ = v___x_3714_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_del_object(v___x_3696_);
lean_dec(v_snd_3694_);
v_a_3720_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3699_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3699_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3730_, lean_object* v_elimTrivial_3731_, lean_object* v_as_3732_, lean_object* v_sz_3733_, lean_object* v_i_3734_, lean_object* v_b_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
uint8_t v_elimTrivial_boxed_3741_; size_t v_sz_boxed_3742_; size_t v_i_boxed_3743_; lean_object* v_res_3744_; 
v_elimTrivial_boxed_3741_ = lean_unbox(v_elimTrivial_3731_);
v_sz_boxed_3742_ = lean_unbox_usize(v_sz_3733_);
lean_dec(v_sz_3733_);
v_i_boxed_3743_ = lean_unbox_usize(v_i_3734_);
lean_dec(v_i_3734_);
v_res_3744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3730_, v_elimTrivial_boxed_3741_, v_as_3732_, v_sz_boxed_3742_, v_i_boxed_3743_, v_b_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec_ref(v_as_3732_);
lean_dec_ref(v_init_3730_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3745_, lean_object* v_elimTrivial_3746_, lean_object* v_n_3747_, lean_object* v_b_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
uint8_t v_elimTrivial_boxed_3754_; lean_object* v_res_3755_; 
v_elimTrivial_boxed_3754_ = lean_unbox(v_elimTrivial_3746_);
v_res_3755_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3745_, v_elimTrivial_boxed_3754_, v_n_3747_, v_b_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec_ref(v_n_3747_);
lean_dec_ref(v_init_3745_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3756_, lean_object* v_t_3757_, lean_object* v_init_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_root_3764_; lean_object* v_tail_3765_; lean_object* v___x_3766_; 
v_root_3764_ = lean_ctor_get(v_t_3757_, 0);
v_tail_3765_ = lean_ctor_get(v_t_3757_, 1);
lean_inc_ref(v_init_3758_);
v___x_3766_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3758_, v_elimTrivial_3756_, v_root_3764_, v_init_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec_ref(v_init_3758_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3803_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3803_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3803_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
if (lean_obj_tag(v_a_3767_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3773_; 
v_a_3771_ = lean_ctor_get(v_a_3767_, 0);
lean_inc(v_a_3771_);
lean_dec_ref_known(v_a_3767_, 1);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v_a_3771_);
v___x_3773_ = v___x_3769_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; size_t v_sz_3778_; size_t v___x_3779_; lean_object* v___x_3780_; 
lean_del_object(v___x_3769_);
v_a_3775_ = lean_ctor_get(v_a_3767_, 0);
lean_inc(v_a_3775_);
lean_dec_ref_known(v_a_3767_, 1);
v___x_3776_ = lean_box(0);
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
lean_ctor_set(v___x_3777_, 1, v_a_3775_);
v_sz_3778_ = lean_array_size(v_tail_3765_);
v___x_3779_ = ((size_t)0ULL);
v___x_3780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3756_, v_tail_3765_, v_sz_3778_, v___x_3779_, v___x_3777_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3794_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3783_ = v___x_3780_;
v_isShared_3784_ = v_isSharedCheck_3794_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3780_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3794_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v_fst_3785_; 
v_fst_3785_ = lean_ctor_get(v_a_3781_, 0);
if (lean_obj_tag(v_fst_3785_) == 0)
{
lean_object* v_snd_3786_; lean_object* v___x_3788_; 
v_snd_3786_ = lean_ctor_get(v_a_3781_, 1);
lean_inc(v_snd_3786_);
lean_dec(v_a_3781_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v_snd_3786_);
v___x_3788_ = v___x_3783_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_snd_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
else
{
lean_object* v_val_3790_; lean_object* v___x_3792_; 
lean_inc_ref(v_fst_3785_);
lean_dec(v_a_3781_);
v_val_3790_ = lean_ctor_get(v_fst_3785_, 0);
lean_inc(v_val_3790_);
lean_dec_ref_known(v_fst_3785_, 1);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v_val_3790_);
v___x_3792_ = v___x_3783_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_val_3790_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
v_a_3795_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3780_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3780_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
v_a_3804_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3766_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3766_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_3812_, lean_object* v_t_3813_, lean_object* v_init_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
uint8_t v_elimTrivial_boxed_3820_; lean_object* v_res_3821_; 
v_elimTrivial_boxed_3820_ = lean_unbox(v_elimTrivial_3812_);
v_res_3821_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_3820_, v_t_3813_, v_init_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec_ref(v_t_3813_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_3822_, size_t v_sz_3823_, size_t v_i_3824_, lean_object* v_b_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
uint8_t v___x_3831_; 
v___x_3831_ = lean_usize_dec_lt(v_i_3824_, v_sz_3823_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; 
v___x_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3832_, 0, v_b_3825_);
return v___x_3832_;
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v_a_3833_ = lean_array_uget_borrowed(v_as_3822_, v_i_3824_);
v___x_3834_ = l_Lean_Expr_fvarId_x21(v_a_3833_);
v___x_3835_ = l_Lean_MVarId_tryClear(v_b_3825_, v___x_3834_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; size_t v___x_3837_; size_t v___x_3838_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref_known(v___x_3835_, 1);
v___x_3837_ = ((size_t)1ULL);
v___x_3838_ = lean_usize_add(v_i_3824_, v___x_3837_);
v_i_3824_ = v___x_3838_;
v_b_3825_ = v_a_3836_;
goto _start;
}
else
{
return v___x_3835_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_3840_, lean_object* v_sz_3841_, lean_object* v_i_3842_, lean_object* v_b_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
size_t v_sz_boxed_3849_; size_t v_i_boxed_3850_; lean_object* v_res_3851_; 
v_sz_boxed_3849_ = lean_unbox_usize(v_sz_3841_);
lean_dec(v_sz_3841_);
v_i_boxed_3850_ = lean_unbox_usize(v_i_3842_);
lean_dec(v_i_3842_);
v_res_3851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3840_, v_sz_boxed_3849_, v_i_boxed_3850_, v_b_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v_as_3840_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_3852_, lean_object* v_x_3853_, lean_object* v_x_3854_, lean_object* v_x_3855_){
_start:
{
lean_object* v_ks_3856_; lean_object* v_vs_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3881_; 
v_ks_3856_ = lean_ctor_get(v_x_3852_, 0);
v_vs_3857_ = lean_ctor_get(v_x_3852_, 1);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_x_3852_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3859_ = v_x_3852_;
v_isShared_3860_ = v_isSharedCheck_3881_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_vs_3857_);
lean_inc(v_ks_3856_);
lean_dec(v_x_3852_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3881_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3861_; uint8_t v___x_3862_; 
v___x_3861_ = lean_array_get_size(v_ks_3856_);
v___x_3862_ = lean_nat_dec_lt(v_x_3853_, v___x_3861_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3866_; 
lean_dec(v_x_3853_);
v___x_3863_ = lean_array_push(v_ks_3856_, v_x_3854_);
v___x_3864_ = lean_array_push(v_vs_3857_, v_x_3855_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 1, v___x_3864_);
lean_ctor_set(v___x_3859_, 0, v___x_3863_);
v___x_3866_ = v___x_3859_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3863_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v___x_3864_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
else
{
lean_object* v_k_x27_3868_; uint8_t v___x_3869_; 
v_k_x27_3868_ = lean_array_fget_borrowed(v_ks_3856_, v_x_3853_);
v___x_3869_ = l_Lean_instBEqMVarId_beq(v_x_3854_, v_k_x27_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3871_; 
if (v_isShared_3860_ == 0)
{
v___x_3871_ = v___x_3859_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_ks_3856_);
lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_vs_3857_);
v___x_3871_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = lean_unsigned_to_nat(1u);
v___x_3873_ = lean_nat_add(v_x_3853_, v___x_3872_);
lean_dec(v_x_3853_);
v_x_3852_ = v___x_3871_;
v_x_3853_ = v___x_3873_;
goto _start;
}
}
else
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3876_ = lean_array_fset(v_ks_3856_, v_x_3853_, v_x_3854_);
v___x_3877_ = lean_array_fset(v_vs_3857_, v_x_3853_, v_x_3855_);
lean_dec(v_x_3853_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 1, v___x_3877_);
lean_ctor_set(v___x_3859_, 0, v___x_3876_);
v___x_3879_ = v___x_3859_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___x_3877_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_3882_, lean_object* v_k_3883_, lean_object* v_v_3884_){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = lean_unsigned_to_nat(0u);
v___x_3886_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_3882_, v___x_3885_, v_k_3883_, v_v_3884_);
return v___x_3886_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_3888_, size_t v_x_3889_, size_t v_x_3890_, lean_object* v_x_3891_, lean_object* v_x_3892_){
_start:
{
if (lean_obj_tag(v_x_3888_) == 0)
{
lean_object* v_es_3893_; size_t v___x_3894_; size_t v___x_3895_; lean_object* v_j_3896_; lean_object* v___x_3897_; uint8_t v___x_3898_; 
v_es_3893_ = lean_ctor_get(v_x_3888_, 0);
v___x_3894_ = ((size_t)31ULL);
v___x_3895_ = lean_usize_land(v_x_3889_, v___x_3894_);
v_j_3896_ = lean_usize_to_nat(v___x_3895_);
v___x_3897_ = lean_array_get_size(v_es_3893_);
v___x_3898_ = lean_nat_dec_lt(v_j_3896_, v___x_3897_);
if (v___x_3898_ == 0)
{
lean_dec(v_j_3896_);
lean_dec(v_x_3892_);
lean_dec(v_x_3891_);
return v_x_3888_;
}
else
{
lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3937_; 
lean_inc_ref(v_es_3893_);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_x_3888_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; 
v_unused_3938_ = lean_ctor_get(v_x_3888_, 0);
lean_dec(v_unused_3938_);
v___x_3900_ = v_x_3888_;
v_isShared_3901_ = v_isSharedCheck_3937_;
goto v_resetjp_3899_;
}
else
{
lean_dec(v_x_3888_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3937_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v_v_3902_; lean_object* v___x_3903_; lean_object* v_xs_x27_3904_; lean_object* v___y_3906_; 
v_v_3902_ = lean_array_fget(v_es_3893_, v_j_3896_);
v___x_3903_ = lean_box(0);
v_xs_x27_3904_ = lean_array_fset(v_es_3893_, v_j_3896_, v___x_3903_);
switch(lean_obj_tag(v_v_3902_))
{
case 0:
{
lean_object* v_key_3911_; lean_object* v_val_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3922_; 
v_key_3911_ = lean_ctor_get(v_v_3902_, 0);
v_val_3912_ = lean_ctor_get(v_v_3902_, 1);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_v_3902_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3914_ = v_v_3902_;
v_isShared_3915_ = v_isSharedCheck_3922_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_val_3912_);
lean_inc(v_key_3911_);
lean_dec(v_v_3902_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3922_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
uint8_t v___x_3916_; 
v___x_3916_ = l_Lean_instBEqMVarId_beq(v_x_3891_, v_key_3911_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_del_object(v___x_3914_);
v___x_3917_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3911_, v_val_3912_, v_x_3891_, v_x_3892_);
v___x_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
v___y_3906_ = v___x_3918_;
goto v___jp_3905_;
}
else
{
lean_object* v___x_3920_; 
lean_dec(v_val_3912_);
lean_dec(v_key_3911_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 1, v_x_3892_);
lean_ctor_set(v___x_3914_, 0, v_x_3891_);
v___x_3920_ = v___x_3914_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_x_3891_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v_x_3892_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
v___y_3906_ = v___x_3920_;
goto v___jp_3905_;
}
}
}
}
case 1:
{
lean_object* v_node_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3935_; 
v_node_3923_ = lean_ctor_get(v_v_3902_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_v_3902_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3925_ = v_v_3902_;
v_isShared_3926_ = v_isSharedCheck_3935_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_node_3923_);
lean_dec(v_v_3902_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3935_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
size_t v___x_3927_; size_t v___x_3928_; size_t v___x_3929_; size_t v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3933_; 
v___x_3927_ = ((size_t)5ULL);
v___x_3928_ = lean_usize_shift_right(v_x_3889_, v___x_3927_);
v___x_3929_ = ((size_t)1ULL);
v___x_3930_ = lean_usize_add(v_x_3890_, v___x_3929_);
v___x_3931_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_3923_, v___x_3928_, v___x_3930_, v_x_3891_, v_x_3892_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3931_);
v___x_3933_ = v___x_3925_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3931_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
v___y_3906_ = v___x_3933_;
goto v___jp_3905_;
}
}
}
default: 
{
lean_object* v___x_3936_; 
v___x_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3936_, 0, v_x_3891_);
lean_ctor_set(v___x_3936_, 1, v_x_3892_);
v___y_3906_ = v___x_3936_;
goto v___jp_3905_;
}
}
v___jp_3905_:
{
lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3907_ = lean_array_fset(v_xs_x27_3904_, v_j_3896_, v___y_3906_);
lean_dec(v_j_3896_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3907_);
v___x_3909_ = v___x_3900_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
else
{
lean_object* v_ks_3939_; lean_object* v_vs_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3958_; 
v_ks_3939_ = lean_ctor_get(v_x_3888_, 0);
v_vs_3940_ = lean_ctor_get(v_x_3888_, 1);
v_isSharedCheck_3958_ = !lean_is_exclusive(v_x_3888_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3942_ = v_x_3888_;
v_isShared_3943_ = v_isSharedCheck_3958_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_vs_3940_);
lean_inc(v_ks_3939_);
lean_dec(v_x_3888_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3958_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_ks_3939_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v_vs_3940_);
v___x_3945_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
lean_object* v_newNode_3946_; size_t v___x_3947_; uint8_t v___x_3948_; 
v_newNode_3946_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_3945_, v_x_3891_, v_x_3892_);
v___x_3947_ = ((size_t)7ULL);
v___x_3948_ = lean_usize_dec_le(v___x_3947_, v_x_3890_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; 
v___x_3949_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3946_);
v___x_3950_ = lean_unsigned_to_nat(4u);
v___x_3951_ = lean_nat_dec_lt(v___x_3949_, v___x_3950_);
lean_dec(v___x_3949_);
if (v___x_3951_ == 0)
{
lean_object* v_ks_3952_; lean_object* v_vs_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v_ks_3952_ = lean_ctor_get(v_newNode_3946_, 0);
lean_inc_ref(v_ks_3952_);
v_vs_3953_ = lean_ctor_get(v_newNode_3946_, 1);
lean_inc_ref(v_vs_3953_);
lean_dec_ref(v_newNode_3946_);
v___x_3954_ = lean_unsigned_to_nat(0u);
v___x_3955_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_3956_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3890_, v_ks_3952_, v_vs_3953_, v___x_3954_, v___x_3955_);
lean_dec_ref(v_vs_3953_);
lean_dec_ref(v_ks_3952_);
return v___x_3956_;
}
else
{
return v_newNode_3946_;
}
}
else
{
return v_newNode_3946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_3959_, lean_object* v_keys_3960_, lean_object* v_vals_3961_, lean_object* v_i_3962_, lean_object* v_entries_3963_){
_start:
{
lean_object* v___x_3964_; uint8_t v___x_3965_; 
v___x_3964_ = lean_array_get_size(v_keys_3960_);
v___x_3965_ = lean_nat_dec_lt(v_i_3962_, v___x_3964_);
if (v___x_3965_ == 0)
{
lean_dec(v_i_3962_);
return v_entries_3963_;
}
else
{
lean_object* v_k_3966_; lean_object* v_v_3967_; uint64_t v___x_3968_; size_t v_h_3969_; size_t v___x_3970_; lean_object* v___x_3971_; size_t v___x_3972_; size_t v___x_3973_; size_t v___x_3974_; size_t v_h_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v_k_3966_ = lean_array_fget_borrowed(v_keys_3960_, v_i_3962_);
v_v_3967_ = lean_array_fget_borrowed(v_vals_3961_, v_i_3962_);
v___x_3968_ = l_Lean_instHashableMVarId_hash(v_k_3966_);
v_h_3969_ = lean_uint64_to_usize(v___x_3968_);
v___x_3970_ = ((size_t)5ULL);
v___x_3971_ = lean_unsigned_to_nat(1u);
v___x_3972_ = ((size_t)1ULL);
v___x_3973_ = lean_usize_sub(v_depth_3959_, v___x_3972_);
v___x_3974_ = lean_usize_mul(v___x_3970_, v___x_3973_);
v_h_3975_ = lean_usize_shift_right(v_h_3969_, v___x_3974_);
v___x_3976_ = lean_nat_add(v_i_3962_, v___x_3971_);
lean_dec(v_i_3962_);
lean_inc(v_v_3967_);
lean_inc(v_k_3966_);
v___x_3977_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_3963_, v_h_3975_, v_depth_3959_, v_k_3966_, v_v_3967_);
v_i_3962_ = v___x_3976_;
v_entries_3963_ = v___x_3977_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_3979_, lean_object* v_keys_3980_, lean_object* v_vals_3981_, lean_object* v_i_3982_, lean_object* v_entries_3983_){
_start:
{
size_t v_depth_boxed_3984_; lean_object* v_res_3985_; 
v_depth_boxed_3984_ = lean_unbox_usize(v_depth_3979_);
lean_dec(v_depth_3979_);
v_res_3985_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_3984_, v_keys_3980_, v_vals_3981_, v_i_3982_, v_entries_3983_);
lean_dec_ref(v_vals_3981_);
lean_dec_ref(v_keys_3980_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_3986_, lean_object* v_x_3987_, lean_object* v_x_3988_, lean_object* v_x_3989_, lean_object* v_x_3990_){
_start:
{
size_t v_x_7803__boxed_3991_; size_t v_x_7804__boxed_3992_; lean_object* v_res_3993_; 
v_x_7803__boxed_3991_ = lean_unbox_usize(v_x_3987_);
lean_dec(v_x_3987_);
v_x_7804__boxed_3992_ = lean_unbox_usize(v_x_3988_);
lean_dec(v_x_3988_);
v_res_3993_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_3986_, v_x_7803__boxed_3991_, v_x_7804__boxed_3992_, v_x_3989_, v_x_3990_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_3994_, lean_object* v_x_3995_, lean_object* v_x_3996_){
_start:
{
uint64_t v___x_3997_; size_t v___x_3998_; size_t v___x_3999_; lean_object* v___x_4000_; 
v___x_3997_ = l_Lean_instHashableMVarId_hash(v_x_3995_);
v___x_3998_ = lean_uint64_to_usize(v___x_3997_);
v___x_3999_ = ((size_t)1ULL);
v___x_4000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_3994_, v___x_3998_, v___x_3999_, v_x_3995_, v_x_3996_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4001_, lean_object* v_val_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; lean_object* v_mctx_4006_; lean_object* v_cache_4007_; lean_object* v_zetaDeltaFVarIds_4008_; lean_object* v_postponed_4009_; lean_object* v_diag_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4039_; 
v___x_4005_ = lean_st_ref_take(v___y_4003_);
v_mctx_4006_ = lean_ctor_get(v___x_4005_, 0);
v_cache_4007_ = lean_ctor_get(v___x_4005_, 1);
v_zetaDeltaFVarIds_4008_ = lean_ctor_get(v___x_4005_, 2);
v_postponed_4009_ = lean_ctor_get(v___x_4005_, 3);
v_diag_4010_ = lean_ctor_get(v___x_4005_, 4);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4012_ = v___x_4005_;
v_isShared_4013_ = v_isSharedCheck_4039_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_diag_4010_);
lean_inc(v_postponed_4009_);
lean_inc(v_zetaDeltaFVarIds_4008_);
lean_inc(v_cache_4007_);
lean_inc(v_mctx_4006_);
lean_dec(v___x_4005_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4039_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v_depth_4014_; lean_object* v_levelAssignDepth_4015_; lean_object* v_lmvarCounter_4016_; lean_object* v_mvarCounter_4017_; lean_object* v_lDecls_4018_; lean_object* v_decls_4019_; lean_object* v_userNames_4020_; lean_object* v_lAssignment_4021_; lean_object* v_eAssignment_4022_; lean_object* v_dAssignment_4023_; lean_object* v_instanceTypedMVars_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4038_; 
v_depth_4014_ = lean_ctor_get(v_mctx_4006_, 0);
v_levelAssignDepth_4015_ = lean_ctor_get(v_mctx_4006_, 1);
v_lmvarCounter_4016_ = lean_ctor_get(v_mctx_4006_, 2);
v_mvarCounter_4017_ = lean_ctor_get(v_mctx_4006_, 3);
v_lDecls_4018_ = lean_ctor_get(v_mctx_4006_, 4);
v_decls_4019_ = lean_ctor_get(v_mctx_4006_, 5);
v_userNames_4020_ = lean_ctor_get(v_mctx_4006_, 6);
v_lAssignment_4021_ = lean_ctor_get(v_mctx_4006_, 7);
v_eAssignment_4022_ = lean_ctor_get(v_mctx_4006_, 8);
v_dAssignment_4023_ = lean_ctor_get(v_mctx_4006_, 9);
v_instanceTypedMVars_4024_ = lean_ctor_get(v_mctx_4006_, 10);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_mctx_4006_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4026_ = v_mctx_4006_;
v_isShared_4027_ = v_isSharedCheck_4038_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_instanceTypedMVars_4024_);
lean_inc(v_dAssignment_4023_);
lean_inc(v_eAssignment_4022_);
lean_inc(v_lAssignment_4021_);
lean_inc(v_userNames_4020_);
lean_inc(v_decls_4019_);
lean_inc(v_lDecls_4018_);
lean_inc(v_mvarCounter_4017_);
lean_inc(v_lmvarCounter_4016_);
lean_inc(v_levelAssignDepth_4015_);
lean_inc(v_depth_4014_);
lean_dec(v_mctx_4006_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4038_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4028_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4022_, v_mvarId_4001_, v_val_4002_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 8, v___x_4028_);
v___x_4030_ = v___x_4026_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_depth_4014_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v_levelAssignDepth_4015_);
lean_ctor_set(v_reuseFailAlloc_4037_, 2, v_lmvarCounter_4016_);
lean_ctor_set(v_reuseFailAlloc_4037_, 3, v_mvarCounter_4017_);
lean_ctor_set(v_reuseFailAlloc_4037_, 4, v_lDecls_4018_);
lean_ctor_set(v_reuseFailAlloc_4037_, 5, v_decls_4019_);
lean_ctor_set(v_reuseFailAlloc_4037_, 6, v_userNames_4020_);
lean_ctor_set(v_reuseFailAlloc_4037_, 7, v_lAssignment_4021_);
lean_ctor_set(v_reuseFailAlloc_4037_, 8, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4037_, 9, v_dAssignment_4023_);
lean_ctor_set(v_reuseFailAlloc_4037_, 10, v_instanceTypedMVars_4024_);
v___x_4030_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4032_; 
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4030_);
v___x_4032_ = v___x_4012_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4030_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_cache_4007_);
lean_ctor_set(v_reuseFailAlloc_4036_, 2, v_zetaDeltaFVarIds_4008_);
lean_ctor_set(v_reuseFailAlloc_4036_, 3, v_postponed_4009_);
lean_ctor_set(v_reuseFailAlloc_4036_, 4, v_diag_4010_);
v___x_4032_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4033_ = lean_st_ref_put(v___y_4003_, v___x_4032_);
v___x_4034_ = lean_box(0);
v___x_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
return v___x_4035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4040_, lean_object* v_val_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4040_, v_val_4041_, v___y_4042_);
lean_dec(v___y_4042_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4047_, uint8_t v_elimTrivial_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; 
lean_inc(v_mvar_4047_);
v___x_4054_ = l_Lean_MVarId_getType(v_mvar_4047_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
lean_inc(v_a_4055_);
lean_dec_ref_known(v___x_4054_, 1);
v___x_4056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4057_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4055_, v___x_4056_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4058_; lean_object* v_fst_4059_; lean_object* v_snd_4060_; lean_object* v_lctx_4061_; lean_object* v___x_4062_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref_known(v___x_4057_, 1);
v_fst_4059_ = lean_ctor_get(v_a_4058_, 0);
lean_inc(v_fst_4059_);
v_snd_4060_ = lean_ctor_get(v_a_4058_, 1);
lean_inc(v_snd_4060_);
lean_dec(v_a_4058_);
v_lctx_4061_ = lean_ctor_get(v___y_4049_, 2);
lean_inc_ref(v_lctx_4061_);
v___x_4062_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4061_, v_snd_4060_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4064_; lean_object* v_decls_4065_; lean_object* v___x_4066_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref_known(v___x_4062_, 1);
v___x_4064_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4065_ = lean_ctor_get(v_a_4063_, 1);
lean_inc_ref(v_decls_4065_);
lean_dec(v_a_4063_);
v___x_4066_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4048_, v_decls_4065_, v___x_4064_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
lean_dec_ref(v_decls_4065_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v_fst_4068_; lean_object* v_snd_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 1);
v_fst_4068_ = lean_ctor_get(v_a_4067_, 0);
lean_inc(v_fst_4068_);
v_snd_4069_ = lean_ctor_get(v_a_4067_, 1);
lean_inc(v_snd_4069_);
lean_dec(v_a_4067_);
v___x_4070_ = l_Lean_Expr_replaceFVars(v_fst_4059_, v_fst_4068_, v_snd_4069_);
lean_dec(v_snd_4069_);
lean_dec(v_fst_4059_);
v___x_4071_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4070_, v_elimTrivial_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4073_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
lean_inc(v_mvar_4047_);
v___x_4073_ = l_Lean_MVarId_getTag(v_mvar_4047_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4075_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4073_, 1);
v___x_4075_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4072_, v_a_4074_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; size_t v_sz_4079_; size_t v___x_4080_; lean_object* v___x_4081_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc_n(v_a_4076_, 2);
lean_dec_ref_known(v___x_4075_, 1);
v___x_4077_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4047_, v_a_4076_, v___y_4050_);
lean_dec_ref(v___x_4077_);
v___x_4078_ = l_Lean_Expr_mvarId_x21(v_a_4076_);
lean_dec(v_a_4076_);
v_sz_4079_ = lean_array_size(v_fst_4068_);
v___x_4080_ = ((size_t)0ULL);
v___x_4081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4068_, v_sz_4079_, v___x_4080_, v___x_4078_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
lean_dec_ref(v___y_4049_);
lean_dec(v_fst_4068_);
return v___x_4081_;
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec(v_fst_4068_);
lean_dec_ref(v___y_4049_);
lean_dec(v_mvar_4047_);
v_a_4082_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4075_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4075_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec(v_a_4072_);
lean_dec(v_fst_4068_);
lean_dec_ref(v___y_4049_);
lean_dec(v_mvar_4047_);
v_a_4090_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4073_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4073_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec(v_fst_4068_);
lean_dec_ref(v___y_4049_);
lean_dec(v_mvar_4047_);
v_a_4098_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4071_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4071_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
else
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4113_; 
lean_dec(v_fst_4059_);
lean_dec_ref(v___y_4049_);
lean_dec(v_mvar_4047_);
v_a_4106_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4108_ = v___x_4066_;
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4066_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4106_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
lean_dec(v_fst_4059_);
lean_dec_ref(v___y_4049_);
lean_dec(v_mvar_4047_);
v_a_4114_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4062_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4062_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_dec_ref(v___y_4049_);
lean_dec(v_mvar_4047_);
v_a_4122_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4057_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4057_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec_ref(v___y_4049_);
lean_dec(v_mvar_4047_);
v_a_4130_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4054_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4054_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4138_, lean_object* v_elimTrivial_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
uint8_t v_elimTrivial_boxed_4145_; lean_object* v_res_4146_; 
v_elimTrivial_boxed_4145_ = lean_unbox(v_elimTrivial_4139_);
v_res_4146_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4138_, v_elimTrivial_boxed_4145_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4147_, uint8_t v_elimTrivial_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v___x_4154_; lean_object* v___f_4155_; lean_object* v___x_4156_; 
v___x_4154_ = lean_box(v_elimTrivial_4148_);
lean_inc(v_mvar_4147_);
v___f_4155_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4155_, 0, v_mvar_4147_);
lean_closure_set(v___f_4155_, 1, v___x_4154_);
v___x_4156_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4147_, v___f_4155_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4157_, lean_object* v_elimTrivial_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
uint8_t v_elimTrivial_boxed_4164_; lean_object* v_res_4165_; 
v_elimTrivial_boxed_4164_ = lean_unbox(v_elimTrivial_4158_);
v_res_4165_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4157_, v_elimTrivial_boxed_4164_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4166_, lean_object* v_val_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4166_, v_val_4167_, v___y_4169_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4174_, lean_object* v_val_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4174_, v_val_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4182_, lean_object* v_x_4183_, lean_object* v_x_4184_, lean_object* v_x_4185_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4183_, v_x_4184_, v_x_4185_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4187_, lean_object* v_as_4188_, size_t v_sz_4189_, size_t v_i_4190_, lean_object* v_b_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4187_, v_as_4188_, v_sz_4189_, v_i_4190_, v_b_4191_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4198_, lean_object* v_as_4199_, lean_object* v_sz_4200_, lean_object* v_i_4201_, lean_object* v_b_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
uint8_t v_elimTrivial_boxed_4208_; size_t v_sz_boxed_4209_; size_t v_i_boxed_4210_; lean_object* v_res_4211_; 
v_elimTrivial_boxed_4208_ = lean_unbox(v_elimTrivial_4198_);
v_sz_boxed_4209_ = lean_unbox_usize(v_sz_4200_);
lean_dec(v_sz_4200_);
v_i_boxed_4210_ = lean_unbox_usize(v_i_4201_);
lean_dec(v_i_4201_);
v_res_4211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4208_, v_as_4199_, v_sz_boxed_4209_, v_i_boxed_4210_, v_b_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
lean_dec_ref(v_as_4199_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4212_, lean_object* v_x_4213_, size_t v_x_4214_, size_t v_x_4215_, lean_object* v_x_4216_, lean_object* v_x_4217_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4213_, v_x_4214_, v_x_4215_, v_x_4216_, v_x_4217_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4219_, lean_object* v_x_4220_, lean_object* v_x_4221_, lean_object* v_x_4222_, lean_object* v_x_4223_, lean_object* v_x_4224_){
_start:
{
size_t v_x_8249__boxed_4225_; size_t v_x_8250__boxed_4226_; lean_object* v_res_4227_; 
v_x_8249__boxed_4225_ = lean_unbox_usize(v_x_4221_);
lean_dec(v_x_4221_);
v_x_8250__boxed_4226_ = lean_unbox_usize(v_x_4222_);
lean_dec(v_x_4222_);
v_res_4227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4219_, v_x_4220_, v_x_8249__boxed_4225_, v_x_8250__boxed_4226_, v_x_4223_, v_x_4224_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4228_, lean_object* v_as_4229_, size_t v_sz_4230_, size_t v_i_4231_, lean_object* v_b_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4228_, v_as_4229_, v_sz_4230_, v_i_4231_, v_b_4232_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4239_, lean_object* v_as_4240_, lean_object* v_sz_4241_, lean_object* v_i_4242_, lean_object* v_b_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
uint8_t v_elimTrivial_boxed_4249_; size_t v_sz_boxed_4250_; size_t v_i_boxed_4251_; lean_object* v_res_4252_; 
v_elimTrivial_boxed_4249_ = lean_unbox(v_elimTrivial_4239_);
v_sz_boxed_4250_ = lean_unbox_usize(v_sz_4241_);
lean_dec(v_sz_4241_);
v_i_boxed_4251_ = lean_unbox_usize(v_i_4242_);
lean_dec(v_i_4242_);
v_res_4252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4249_, v_as_4240_, v_sz_boxed_4250_, v_i_boxed_4251_, v_b_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec_ref(v_as_4240_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4253_, lean_object* v_n_4254_, lean_object* v_k_4255_, lean_object* v_v_4256_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4254_, v_k_4255_, v_v_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4258_, size_t v_depth_4259_, lean_object* v_keys_4260_, lean_object* v_vals_4261_, lean_object* v_heq_4262_, lean_object* v_i_4263_, lean_object* v_entries_4264_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4259_, v_keys_4260_, v_vals_4261_, v_i_4263_, v_entries_4264_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4266_, lean_object* v_depth_4267_, lean_object* v_keys_4268_, lean_object* v_vals_4269_, lean_object* v_heq_4270_, lean_object* v_i_4271_, lean_object* v_entries_4272_){
_start:
{
size_t v_depth_boxed_4273_; lean_object* v_res_4274_; 
v_depth_boxed_4273_ = lean_unbox_usize(v_depth_4267_);
lean_dec(v_depth_4267_);
v_res_4274_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4266_, v_depth_boxed_4273_, v_keys_4268_, v_vals_4269_, v_heq_4270_, v_i_4271_, v_entries_4272_);
lean_dec_ref(v_vals_4269_);
lean_dec_ref(v_keys_4268_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4275_, lean_object* v_x_4276_, lean_object* v_x_4277_, lean_object* v_x_4278_, lean_object* v_x_4279_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4276_, v_x_4277_, v_x_4278_, v_x_4279_);
return v___x_4280_;
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
