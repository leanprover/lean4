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
lean_object* v___x_628_; lean_object* v_env_629_; lean_object* v___x_630_; lean_object* v_mctx_631_; lean_object* v_lctx_632_; lean_object* v_options_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_628_ = lean_st_ref_get(v___y_626_);
v_env_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc_ref(v_env_629_);
lean_dec(v___x_628_);
v___x_630_ = lean_st_ref_get(v___y_624_);
v_mctx_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc_ref(v_mctx_631_);
lean_dec(v___x_630_);
v_lctx_632_ = lean_ctor_get(v___y_623_, 2);
v_options_633_ = lean_ctor_get(v___y_625_, 2);
lean_inc_ref(v_options_633_);
lean_inc_ref(v_lctx_632_);
v___x_634_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_634_, 0, v_env_629_);
lean_ctor_set(v___x_634_, 1, v_mctx_631_);
lean_ctor_set(v___x_634_, 2, v_lctx_632_);
lean_ctor_set(v___x_634_, 3, v_options_633_);
v___x_635_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_msgData_622_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object* v_msgData_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object* v_msg_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_ref_650_; lean_object* v___x_651_; lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_ref_650_ = lean_ctor_get(v___y_647_, 5);
v___x_651_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msg_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
lean_inc(v_ref_650_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_ref_650_);
lean_ctor_set(v___x_656_, 1, v_a_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 1);
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object* v_data_668_, lean_object* v_expr_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Expr_mdata___override(v_data_668_, v_expr_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object* v_typeName_671_, lean_object* v_idx_672_, lean_object* v_struct_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_Expr_proj___override(v_typeName_671_, v_idx_672_, v_struct_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object* v_a_675_, lean_object* v_b_676_, lean_object* v_x_677_){
_start:
{
if (lean_obj_tag(v_x_677_) == 0)
{
lean_dec(v_b_676_);
lean_dec(v_a_675_);
return v_x_677_;
}
else
{
lean_object* v_key_678_; lean_object* v_value_679_; lean_object* v_tail_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_692_; 
v_key_678_ = lean_ctor_get(v_x_677_, 0);
v_value_679_ = lean_ctor_get(v_x_677_, 1);
v_tail_680_ = lean_ctor_get(v_x_677_, 2);
v_isSharedCheck_692_ = !lean_is_exclusive(v_x_677_);
if (v_isSharedCheck_692_ == 0)
{
v___x_682_ = v_x_677_;
v_isShared_683_ = v_isSharedCheck_692_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_tail_680_);
lean_inc(v_value_679_);
lean_inc(v_key_678_);
lean_dec(v_x_677_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_692_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___x_684_; 
v___x_684_ = l_Lean_instBEqFVarId_beq(v_key_678_, v_a_675_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_675_, v_b_676_, v_tail_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 2, v___x_685_);
v___x_687_ = v___x_682_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_key_678_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_value_679_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
else
{
lean_object* v___x_690_; 
lean_dec(v_value_679_);
lean_dec(v_key_678_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v_b_676_);
lean_ctor_set(v___x_682_, 0, v_a_675_);
v___x_690_ = v___x_682_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_675_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_b_676_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v_tail_680_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object* v_m_693_, lean_object* v_a_694_, lean_object* v_b_695_){
_start:
{
lean_object* v_size_696_; lean_object* v_buckets_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_740_; 
v_size_696_ = lean_ctor_get(v_m_693_, 0);
v_buckets_697_ = lean_ctor_get(v_m_693_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_m_693_);
if (v_isSharedCheck_740_ == 0)
{
v___x_699_ = v_m_693_;
v_isShared_700_ = v_isSharedCheck_740_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_buckets_697_);
lean_inc(v_size_696_);
lean_dec(v_m_693_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_740_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v_fold_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; size_t v___x_713_; lean_object* v_bkt_714_; uint8_t v___x_715_; 
v___x_701_ = lean_array_get_size(v_buckets_697_);
v___x_702_ = l_Lean_instHashableFVarId_hash(v_a_694_);
v___x_703_ = 32ULL;
v___x_704_ = lean_uint64_shift_right(v___x_702_, v___x_703_);
v_fold_705_ = lean_uint64_xor(v___x_702_, v___x_704_);
v___x_706_ = 16ULL;
v___x_707_ = lean_uint64_shift_right(v_fold_705_, v___x_706_);
v___x_708_ = lean_uint64_xor(v_fold_705_, v___x_707_);
v___x_709_ = lean_uint64_to_usize(v___x_708_);
v___x_710_ = lean_usize_of_nat(v___x_701_);
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_sub(v___x_710_, v___x_711_);
v___x_713_ = lean_usize_land(v___x_709_, v___x_712_);
v_bkt_714_ = lean_array_uget_borrowed(v_buckets_697_, v___x_713_);
v___x_715_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_694_, v_bkt_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v_size_x27_717_; lean_object* v___x_718_; lean_object* v_buckets_x27_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_716_ = lean_unsigned_to_nat(1u);
v_size_x27_717_ = lean_nat_add(v_size_696_, v___x_716_);
lean_dec(v_size_696_);
lean_inc(v_bkt_714_);
v___x_718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_718_, 0, v_a_694_);
lean_ctor_set(v___x_718_, 1, v_b_695_);
lean_ctor_set(v___x_718_, 2, v_bkt_714_);
v_buckets_x27_719_ = lean_array_uset(v_buckets_697_, v___x_713_, v___x_718_);
v___x_720_ = lean_unsigned_to_nat(4u);
v___x_721_ = lean_nat_mul(v_size_x27_717_, v___x_720_);
v___x_722_ = lean_unsigned_to_nat(3u);
v___x_723_ = lean_nat_div(v___x_721_, v___x_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_array_get_size(v_buckets_x27_719_);
v___x_725_ = lean_nat_dec_le(v___x_723_, v___x_724_);
lean_dec(v___x_723_);
if (v___x_725_ == 0)
{
lean_object* v_val_726_; lean_object* v___x_728_; 
v_val_726_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_719_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v_val_726_);
lean_ctor_set(v___x_699_, 0, v_size_x27_717_);
v___x_728_ = v___x_699_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_size_x27_717_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_val_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
lean_object* v___x_731_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v_buckets_x27_719_);
lean_ctor_set(v___x_699_, 0, v_size_x27_717_);
v___x_731_ = v___x_699_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_size_x27_717_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_buckets_x27_719_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
lean_object* v___x_733_; lean_object* v_buckets_x27_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
lean_inc(v_bkt_714_);
v___x_733_ = lean_box(0);
v_buckets_x27_734_ = lean_array_uset(v_buckets_697_, v___x_713_, v___x_733_);
v___x_735_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_694_, v_b_695_, v_bkt_714_);
v___x_736_ = lean_array_uset(v_buckets_x27_734_, v___x_713_, v___x_735_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v___x_736_);
v___x_738_ = v___x_699_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_size_696_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; lean_object* v_ngen_744_; lean_object* v_namePrefix_745_; lean_object* v_idx_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_775_; 
v___x_743_ = lean_st_ref_get(v___y_741_);
v_ngen_744_ = lean_ctor_get(v___x_743_, 2);
lean_inc_ref(v_ngen_744_);
lean_dec(v___x_743_);
v_namePrefix_745_ = lean_ctor_get(v_ngen_744_, 0);
v_idx_746_ = lean_ctor_get(v_ngen_744_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_ngen_744_);
if (v_isSharedCheck_775_ == 0)
{
v___x_748_ = v_ngen_744_;
v_isShared_749_ = v_isSharedCheck_775_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_idx_746_);
lean_inc(v_namePrefix_745_);
lean_dec(v_ngen_744_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_775_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v_env_751_; lean_object* v_nextMacroScope_752_; lean_object* v_auxDeclNGen_753_; lean_object* v_traceState_754_; lean_object* v_cache_755_; lean_object* v_messages_756_; lean_object* v_infoState_757_; lean_object* v_snapshotTasks_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_773_; 
v___x_750_ = lean_st_ref_take(v___y_741_);
v_env_751_ = lean_ctor_get(v___x_750_, 0);
v_nextMacroScope_752_ = lean_ctor_get(v___x_750_, 1);
v_auxDeclNGen_753_ = lean_ctor_get(v___x_750_, 3);
v_traceState_754_ = lean_ctor_get(v___x_750_, 4);
v_cache_755_ = lean_ctor_get(v___x_750_, 5);
v_messages_756_ = lean_ctor_get(v___x_750_, 6);
v_infoState_757_ = lean_ctor_get(v___x_750_, 7);
v_snapshotTasks_758_ = lean_ctor_get(v___x_750_, 8);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v___x_750_, 2);
lean_dec(v_unused_774_);
v___x_760_ = v___x_750_;
v_isShared_761_ = v_isSharedCheck_773_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snapshotTasks_758_);
lean_inc(v_infoState_757_);
lean_inc(v_messages_756_);
lean_inc(v_cache_755_);
lean_inc(v_traceState_754_);
lean_inc(v_auxDeclNGen_753_);
lean_inc(v_nextMacroScope_752_);
lean_inc(v_env_751_);
lean_dec(v___x_750_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_773_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v_r_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
lean_inc(v_idx_746_);
lean_inc(v_namePrefix_745_);
v_r_762_ = l_Lean_Name_num___override(v_namePrefix_745_, v_idx_746_);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v_idx_746_, v___x_763_);
lean_dec(v_idx_746_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_764_);
v___x_766_ = v___x_748_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_namePrefix_745_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_764_);
v___x_766_ = v_reuseFailAlloc_772_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 2, v___x_766_);
v___x_768_ = v___x_760_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_env_751_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_nextMacroScope_752_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_auxDeclNGen_753_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_traceState_754_);
lean_ctor_set(v_reuseFailAlloc_771_, 5, v_cache_755_);
lean_ctor_set(v_reuseFailAlloc_771_, 6, v_messages_756_);
lean_ctor_set(v_reuseFailAlloc_771_, 7, v_infoState_757_);
lean_ctor_set(v_reuseFailAlloc_771_, 8, v_snapshotTasks_758_);
v___x_768_ = v_reuseFailAlloc_771_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_st_ref_put(v___y_741_, v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v_r_762_);
return v___x_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_776_);
lean_dec(v___y_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v___x_784_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_782_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object* v_a_799_, lean_object* v_x_800_){
_start:
{
if (lean_obj_tag(v_x_800_) == 0)
{
return v_x_800_;
}
else
{
lean_object* v_key_801_; lean_object* v_value_802_; lean_object* v_tail_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_812_; 
v_key_801_ = lean_ctor_get(v_x_800_, 0);
v_value_802_ = lean_ctor_get(v_x_800_, 1);
v_tail_803_ = lean_ctor_get(v_x_800_, 2);
v_isSharedCheck_812_ = !lean_is_exclusive(v_x_800_);
if (v_isSharedCheck_812_ == 0)
{
v___x_805_ = v_x_800_;
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_tail_803_);
lean_inc(v_value_802_);
lean_inc(v_key_801_);
lean_dec(v_x_800_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
uint8_t v___x_807_; 
v___x_807_ = l_Lean_instBEqFVarId_beq(v_key_801_, v_a_799_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_799_, v_tail_803_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 2, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_key_801_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_value_802_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
else
{
lean_del_object(v___x_805_);
lean_dec(v_value_802_);
lean_dec(v_key_801_);
return v_tail_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object* v_a_813_, lean_object* v_x_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_813_, v_x_814_);
lean_dec(v_a_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object* v_m_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_size_818_; lean_object* v_buckets_819_; lean_object* v___x_820_; uint64_t v___x_821_; uint64_t v___x_822_; uint64_t v___x_823_; uint64_t v_fold_824_; uint64_t v___x_825_; uint64_t v___x_826_; uint64_t v___x_827_; size_t v___x_828_; size_t v___x_829_; size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; lean_object* v_bkt_833_; uint8_t v___x_834_; 
v_size_818_ = lean_ctor_get(v_m_816_, 0);
v_buckets_819_ = lean_ctor_get(v_m_816_, 1);
v___x_820_ = lean_array_get_size(v_buckets_819_);
v___x_821_ = l_Lean_instHashableFVarId_hash(v_a_817_);
v___x_822_ = 32ULL;
v___x_823_ = lean_uint64_shift_right(v___x_821_, v___x_822_);
v_fold_824_ = lean_uint64_xor(v___x_821_, v___x_823_);
v___x_825_ = 16ULL;
v___x_826_ = lean_uint64_shift_right(v_fold_824_, v___x_825_);
v___x_827_ = lean_uint64_xor(v_fold_824_, v___x_826_);
v___x_828_ = lean_uint64_to_usize(v___x_827_);
v___x_829_ = lean_usize_of_nat(v___x_820_);
v___x_830_ = ((size_t)1ULL);
v___x_831_ = lean_usize_sub(v___x_829_, v___x_830_);
v___x_832_ = lean_usize_land(v___x_828_, v___x_831_);
v_bkt_833_ = lean_array_uget_borrowed(v_buckets_819_, v___x_832_);
v___x_834_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_817_, v_bkt_833_);
if (v___x_834_ == 0)
{
return v_m_816_;
}
else
{
lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_847_; 
lean_inc(v_bkt_833_);
lean_inc_ref(v_buckets_819_);
lean_inc(v_size_818_);
v_isSharedCheck_847_ = !lean_is_exclusive(v_m_816_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; lean_object* v_unused_849_; 
v_unused_848_ = lean_ctor_get(v_m_816_, 1);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_m_816_, 0);
lean_dec(v_unused_849_);
v___x_836_ = v_m_816_;
v_isShared_837_ = v_isSharedCheck_847_;
goto v_resetjp_835_;
}
else
{
lean_dec(v_m_816_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_847_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v_buckets_x27_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_838_ = lean_box(0);
v_buckets_x27_839_ = lean_array_uset(v_buckets_819_, v___x_832_, v___x_838_);
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_sub(v_size_818_, v___x_840_);
lean_dec(v_size_818_);
v___x_842_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_817_, v_bkt_833_);
v___x_843_ = lean_array_uset(v_buckets_x27_839_, v___x_832_, v___x_842_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_843_);
lean_ctor_set(v___x_836_, 0, v___x_841_);
v___x_845_ = v___x_836_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object* v_m_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_850_, v_a_851_);
lean_dec(v_a_851_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object* v_a_853_, lean_object* v_fallback_854_, lean_object* v_x_855_){
_start:
{
if (lean_obj_tag(v_x_855_) == 0)
{
lean_inc(v_fallback_854_);
return v_fallback_854_;
}
else
{
lean_object* v_key_856_; lean_object* v_value_857_; lean_object* v_tail_858_; uint8_t v___x_859_; 
v_key_856_ = lean_ctor_get(v_x_855_, 0);
v_value_857_ = lean_ctor_get(v_x_855_, 1);
v_tail_858_ = lean_ctor_get(v_x_855_, 2);
v___x_859_ = l_Lean_instBEqFVarId_beq(v_key_856_, v_a_853_);
if (v___x_859_ == 0)
{
v_x_855_ = v_tail_858_;
goto _start;
}
else
{
lean_inc(v_value_857_);
return v_value_857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_861_, lean_object* v_fallback_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_861_, v_fallback_862_, v_x_863_);
lean_dec(v_x_863_);
lean_dec(v_fallback_862_);
lean_dec(v_a_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object* v_m_865_, lean_object* v_a_866_, lean_object* v_fallback_867_){
_start:
{
lean_object* v_buckets_868_; lean_object* v___x_869_; uint64_t v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; uint64_t v_fold_873_; uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; size_t v___x_877_; size_t v___x_878_; size_t v___x_879_; size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_buckets_868_ = lean_ctor_get(v_m_865_, 1);
v___x_869_ = lean_array_get_size(v_buckets_868_);
v___x_870_ = l_Lean_instHashableFVarId_hash(v_a_866_);
v___x_871_ = 32ULL;
v___x_872_ = lean_uint64_shift_right(v___x_870_, v___x_871_);
v_fold_873_ = lean_uint64_xor(v___x_870_, v___x_872_);
v___x_874_ = 16ULL;
v___x_875_ = lean_uint64_shift_right(v_fold_873_, v___x_874_);
v___x_876_ = lean_uint64_xor(v_fold_873_, v___x_875_);
v___x_877_ = lean_uint64_to_usize(v___x_876_);
v___x_878_ = lean_usize_of_nat(v___x_869_);
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_sub(v___x_878_, v___x_879_);
v___x_881_ = lean_usize_land(v___x_877_, v___x_880_);
v___x_882_ = lean_array_uget_borrowed(v_buckets_868_, v___x_881_);
v___x_883_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_866_, v_fallback_867_, v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object* v_m_884_, lean_object* v_a_885_, lean_object* v_fallback_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_884_, v_a_885_, v_fallback_886_);
lean_dec(v_fallback_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_m_884_);
return v_res_887_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_box(0);
v___x_892_ = lean_unsigned_to_nat(16u);
v___x_893_ = lean_mk_array(v___x_892_, v___x_891_);
return v___x_893_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_894_);
return v___x_896_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__1(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__0));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__3(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__2));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__5(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__4));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object* v_e_907_, lean_object* v_subst_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
switch(lean_obj_tag(v_e_907_))
{
case 0:
{
lean_object* v_deBruijnIndex_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_deBruijnIndex_914_ = lean_ctor_get(v_e_907_, 0);
v___x_915_ = lean_array_get_size(v_subst_908_);
v___x_916_ = lean_nat_dec_lt(v_deBruijnIndex_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
lean_inc(v_deBruijnIndex_914_);
lean_dec_ref_known(v_e_907_, 1);
lean_dec_ref(v_subst_908_);
v___x_917_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__1, &l_Lean_Elab_Tactic_Do_countUses___closed__1_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__1);
v___x_918_ = l_Nat_reprFast(v_deBruijnIndex_914_);
v___x_919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
v___x_920_ = l_Lean_MessageData_ofFormat(v___x_919_);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_917_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__3, &l_Lean_Elab_Tactic_Do_countUses___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__3);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = l_Nat_reprFast(v___x_915_);
v___x_925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
v___x_926_ = l_Lean_MessageData_ofFormat(v___x_925_);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_923_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_927_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_928_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_sub(v___x_915_, v___x_929_);
v___x_931_ = lean_nat_sub(v___x_930_, v_deBruijnIndex_914_);
lean_dec(v___x_930_);
v___x_932_ = lean_array_fget(v_subst_908_, v___x_931_);
lean_dec(v___x_931_);
lean_dec_ref(v_subst_908_);
v___x_933_ = 1;
v___x_934_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_935_ = lean_box(v___x_933_);
v___x_936_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_934_, v___x_932_, v___x_935_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_e_907_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
return v___x_938_;
}
}
case 1:
{
lean_object* v_fvarId_939_; uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec_ref(v_subst_908_);
v_fvarId_939_ = lean_ctor_get(v_e_907_, 0);
v___x_940_ = 1;
v___x_941_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_942_ = lean_box(v___x_940_);
lean_inc(v_fvarId_939_);
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_941_, v_fvarId_939_, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_e_907_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
case 5:
{
lean_object* v_fn_946_; lean_object* v_arg_947_; lean_object* v___x_948_; 
v_fn_946_ = lean_ctor_get(v_e_907_, 0);
lean_inc_ref(v_fn_946_);
v_arg_947_ = lean_ctor_get(v_e_907_, 1);
lean_inc_ref(v_arg_947_);
lean_dec_ref_known(v_e_907_, 2);
lean_inc_ref(v_subst_908_);
v___x_948_ = l_Lean_Elab_Tactic_Do_countUses(v_fn_946_, v_subst_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v_fst_950_; lean_object* v_snd_951_; lean_object* v___x_952_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v_fst_950_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_fst_950_);
v_snd_951_ = lean_ctor_get(v_a_949_, 1);
lean_inc(v_snd_951_);
lean_dec(v_a_949_);
v___x_952_ = l_Lean_Elab_Tactic_Do_countUses(v_arg_947_, v_subst_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_971_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_971_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_971_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_971_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_fst_957_; lean_object* v_snd_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_970_; 
v_fst_957_ = lean_ctor_get(v_a_953_, 0);
v_snd_958_ = lean_ctor_get(v_a_953_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_a_953_);
if (v_isSharedCheck_970_ == 0)
{
v___x_960_ = v_a_953_;
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_snd_958_);
lean_inc(v_fst_957_);
lean_dec(v_a_953_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_962_ = l_Lean_Expr_app___override(v_fst_950_, v_fst_957_);
v___x_963_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_951_, v_snd_958_);
lean_dec(v_snd_951_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v___x_963_);
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_965_ = v___x_960_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_963_);
v___x_965_ = v_reuseFailAlloc_969_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_967_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_965_);
v___x_967_ = v___x_955_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
else
{
lean_dec(v_snd_951_);
lean_dec(v_fst_950_);
return v___x_952_;
}
}
else
{
lean_dec_ref(v_arg_947_);
lean_dec_ref(v_subst_908_);
return v___x_948_;
}
}
case 6:
{
lean_object* v_binderName_972_; lean_object* v_binderType_973_; lean_object* v_body_974_; uint8_t v_binderInfo_975_; lean_object* v___x_976_; 
v_binderName_972_ = lean_ctor_get(v_e_907_, 0);
lean_inc(v_binderName_972_);
v_binderType_973_ = lean_ctor_get(v_e_907_, 1);
lean_inc_ref(v_binderType_973_);
v_body_974_ = lean_ctor_get(v_e_907_, 2);
lean_inc_ref(v_body_974_);
v_binderInfo_975_ = lean_ctor_get_uint8(v_e_907_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_907_, 3);
v___x_976_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
lean_inc_ref(v_subst_908_);
v___x_978_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_973_, v_subst_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v_fst_980_; lean_object* v_snd_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v_fst_980_ = lean_ctor_get(v_a_979_, 0);
lean_inc(v_fst_980_);
v_snd_981_ = lean_ctor_get(v_a_979_, 1);
lean_inc(v_snd_981_);
lean_dec(v_a_979_);
lean_inc(v_a_977_);
v___x_982_ = lean_array_push(v_subst_908_, v_a_977_);
v___x_983_ = l_Lean_Elab_Tactic_Do_countUses(v_body_974_, v___x_982_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1003_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_1003_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1003_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_fst_988_; lean_object* v_snd_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1002_; 
v_fst_988_ = lean_ctor_get(v_a_984_, 0);
v_snd_989_ = lean_ctor_get(v_a_984_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_a_984_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_991_ = v_a_984_;
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_snd_989_);
lean_inc(v_fst_988_);
lean_dec(v_a_984_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1002_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_993_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_981_, v_snd_989_);
lean_dec(v_snd_981_);
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_993_, v_a_977_);
lean_dec(v_a_977_);
v___x_995_ = l_Lean_Expr_lam___override(v_binderName_972_, v_fst_980_, v_fst_988_, v_binderInfo_975_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___x_994_);
lean_ctor_set(v___x_991_, 0, v___x_995_);
v___x_997_ = v___x_991_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_994_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_997_);
v___x_999_ = v___x_986_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
else
{
lean_dec(v_snd_981_);
lean_dec(v_fst_980_);
lean_dec(v_a_977_);
lean_dec(v_binderName_972_);
return v___x_983_;
}
}
else
{
lean_dec(v_a_977_);
lean_dec_ref(v_body_974_);
lean_dec(v_binderName_972_);
lean_dec_ref(v_subst_908_);
return v___x_978_;
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_body_974_);
lean_dec_ref(v_binderType_973_);
lean_dec(v_binderName_972_);
lean_dec_ref(v_subst_908_);
v_a_1004_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_976_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_976_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1012_; lean_object* v_binderType_1013_; lean_object* v_body_1014_; uint8_t v_binderInfo_1015_; lean_object* v___x_1016_; 
v_binderName_1012_ = lean_ctor_get(v_e_907_, 0);
lean_inc(v_binderName_1012_);
v_binderType_1013_ = lean_ctor_get(v_e_907_, 1);
lean_inc_ref(v_binderType_1013_);
v_body_1014_ = lean_ctor_get(v_e_907_, 2);
lean_inc_ref(v_body_1014_);
v_binderInfo_1015_ = lean_ctor_get_uint8(v_e_907_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_907_, 3);
v___x_1016_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
lean_inc_ref(v_subst_908_);
v___x_1018_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1013_, v_subst_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v_fst_1020_; lean_object* v_snd_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v_fst_1020_ = lean_ctor_get(v_a_1019_, 0);
lean_inc(v_fst_1020_);
v_snd_1021_ = lean_ctor_get(v_a_1019_, 1);
lean_inc(v_snd_1021_);
lean_dec(v_a_1019_);
lean_inc(v_a_1017_);
v___x_1022_ = lean_array_push(v_subst_908_, v_a_1017_);
v___x_1023_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1014_, v___x_1022_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1043_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1043_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1043_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_fst_1028_; lean_object* v_snd_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1042_; 
v_fst_1028_ = lean_ctor_get(v_a_1024_, 0);
v_snd_1029_ = lean_ctor_get(v_a_1024_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_a_1024_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1031_ = v_a_1024_;
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_snd_1029_);
lean_inc(v_fst_1028_);
lean_dec(v_a_1024_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1033_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_1021_, v_snd_1029_);
lean_dec(v_snd_1021_);
v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1033_, v_a_1017_);
lean_dec(v_a_1017_);
v___x_1035_ = l_Lean_Expr_forallE___override(v_binderName_1012_, v_fst_1020_, v_fst_1028_, v_binderInfo_1015_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v___x_1034_);
lean_ctor_set(v___x_1031_, 0, v___x_1035_);
v___x_1037_ = v___x_1031_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1034_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1037_);
v___x_1039_ = v___x_1026_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
else
{
lean_dec(v_snd_1021_);
lean_dec(v_fst_1020_);
lean_dec(v_a_1017_);
lean_dec(v_binderName_1012_);
return v___x_1023_;
}
}
else
{
lean_dec(v_a_1017_);
lean_dec_ref(v_body_1014_);
lean_dec(v_binderName_1012_);
lean_dec_ref(v_subst_908_);
return v___x_1018_;
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v_body_1014_);
lean_dec_ref(v_binderType_1013_);
lean_dec(v_binderName_1012_);
lean_dec_ref(v_subst_908_);
v_a_1044_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1016_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1016_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
case 8:
{
lean_object* v_declName_1052_; lean_object* v_type_1053_; lean_object* v_value_1054_; lean_object* v_body_1055_; uint8_t v_nondep_1056_; lean_object* v___x_1057_; 
v_declName_1052_ = lean_ctor_get(v_e_907_, 0);
lean_inc(v_declName_1052_);
v_type_1053_ = lean_ctor_get(v_e_907_, 1);
lean_inc_ref(v_type_1053_);
v_value_1054_ = lean_ctor_get(v_e_907_, 2);
lean_inc_ref(v_value_1054_);
v_body_1055_ = lean_ctor_get(v_e_907_, 3);
lean_inc_ref(v_body_1055_);
v_nondep_1056_ = lean_ctor_get_uint8(v_e_907_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_907_, 4);
v___x_1057_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc_n(v_a_1058_, 2);
lean_dec_ref_known(v___x_1057_, 1);
lean_inc_ref(v_subst_908_);
v___x_1059_ = lean_array_push(v_subst_908_, v_a_1058_);
v___x_1060_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1055_, v___x_1059_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1103_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1103_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1103_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1068_; 
v_fst_1065_ = lean_ctor_get(v_a_1061_, 0);
lean_inc(v_fst_1065_);
v_snd_1066_ = lean_ctor_get(v_a_1061_, 1);
lean_inc(v_snd_1066_);
lean_dec(v_a_1061_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set_tag(v___x_1063_, 1);
lean_ctor_set(v___x_1063_, 0, v_value_1054_);
v___x_1068_ = v___x_1063_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_value_1054_);
v___x_1068_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_a_1058_, v_type_1053_, v___x_1068_, v_snd_1066_, v_subst_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_1058_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1093_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1093_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1093_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_snd_1074_; lean_object* v_fst_1075_; 
v_snd_1074_ = lean_ctor_get(v_a_1070_, 1);
lean_inc(v_snd_1074_);
v_fst_1075_ = lean_ctor_get(v_snd_1074_, 0);
lean_inc(v_fst_1075_);
if (lean_obj_tag(v_fst_1075_) == 1)
{
lean_object* v_fst_1076_; lean_object* v_snd_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1089_; 
v_fst_1076_ = lean_ctor_get(v_a_1070_, 0);
lean_inc(v_fst_1076_);
lean_dec(v_a_1070_);
v_snd_1077_ = lean_ctor_get(v_snd_1074_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_snd_1074_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v_snd_1074_, 0);
lean_dec(v_unused_1090_);
v___x_1079_ = v_snd_1074_;
v_isShared_1080_ = v_isSharedCheck_1089_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_snd_1077_);
lean_dec(v_snd_1074_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1089_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_val_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v_val_1081_ = lean_ctor_get(v_fst_1075_, 0);
lean_inc(v_val_1081_);
lean_dec_ref_known(v_fst_1075_, 1);
v___x_1082_ = l_Lean_Expr_letE___override(v_declName_1052_, v_fst_1076_, v_val_1081_, v_fst_1065_, v_nondep_1056_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1082_);
v___x_1084_ = v___x_1079_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_snd_1077_);
v___x_1084_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1084_);
v___x_1086_ = v___x_1072_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec(v_fst_1075_);
lean_dec(v_snd_1074_);
lean_del_object(v___x_1072_);
lean_dec(v_a_1070_);
lean_dec(v_fst_1065_);
lean_dec(v_declName_1052_);
v___x_1091_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
v___x_1092_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_1091_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_1092_;
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec(v_fst_1065_);
lean_dec(v_declName_1052_);
v_a_1094_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1069_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1069_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1058_);
lean_dec_ref(v_value_1054_);
lean_dec_ref(v_type_1053_);
lean_dec(v_declName_1052_);
lean_dec_ref(v_subst_908_);
return v___x_1060_;
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v_body_1055_);
lean_dec_ref(v_value_1054_);
lean_dec_ref(v_type_1053_);
lean_dec(v_declName_1052_);
lean_dec_ref(v_subst_908_);
v_a_1104_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1057_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1057_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
case 10:
{
lean_object* v_data_1112_; lean_object* v_expr_1113_; lean_object* v___x_1114_; 
v_data_1112_ = lean_ctor_get(v_e_907_, 0);
lean_inc(v_data_1112_);
v_expr_1113_ = lean_ctor_get(v_e_907_, 1);
lean_inc_ref(v_expr_1113_);
lean_dec_ref_known(v_e_907_, 2);
v___x_1114_ = l_Lean_Elab_Tactic_Do_countUses(v_expr_1113_, v_subst_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1124_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___f_1119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__0), 2, 1);
lean_closure_set(v___f_1119_, 0, v_data_1112_);
v___x_1120_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1119_, v_a_1115_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1120_);
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
lean_dec(v_data_1112_);
return v___x_1114_;
}
}
case 11:
{
lean_object* v_typeName_1125_; lean_object* v_idx_1126_; lean_object* v_struct_1127_; lean_object* v___x_1128_; 
v_typeName_1125_ = lean_ctor_get(v_e_907_, 0);
lean_inc(v_typeName_1125_);
v_idx_1126_ = lean_ctor_get(v_e_907_, 1);
lean_inc(v_idx_1126_);
v_struct_1127_ = lean_ctor_get(v_e_907_, 2);
lean_inc_ref(v_struct_1127_);
lean_dec_ref_known(v_e_907_, 3);
v___x_1128_ = l_Lean_Elab_Tactic_Do_countUses(v_struct_1127_, v_subst_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1138_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1138_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1138_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___f_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___f_1133_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__1), 3, 2);
lean_closure_set(v___f_1133_, 0, v_typeName_1125_);
lean_closure_set(v___f_1133_, 1, v_idx_1126_);
v___x_1134_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1133_, v_a_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
lean_dec(v_idx_1126_);
lean_dec(v_typeName_1125_);
return v___x_1128_;
}
}
default: 
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec_ref(v_subst_908_);
v___x_1139_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_e_907_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object* v_fvarId_1142_, lean_object* v_ty_1143_, lean_object* v_val_x3f_1144_, lean_object* v_bodyUses_1145_, lean_object* v_subst_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1152_; 
lean_inc_ref(v_subst_1146_);
v___x_1152_ = l_Lean_Elab_Tactic_Do_countUses(v_ty_1143_, v_subst_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1208_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1208_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1208_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_fst_1157_; lean_object* v_snd_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1207_; 
v_fst_1157_ = lean_ctor_get(v_a_1153_, 0);
v_snd_1158_ = lean_ctor_get(v_a_1153_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_a_1153_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1160_ = v_a_1153_;
v_isShared_1161_ = v_isSharedCheck_1207_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snd_1158_);
lean_inc(v_fst_1157_);
lean_dec(v_a_1153_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1207_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___y_1163_; uint8_t v___y_1164_; lean_object* v___y_1165_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; 
if (lean_obj_tag(v_val_x3f_1144_) == 0)
{
lean_object* v___x_1191_; 
lean_dec_ref(v_subst_1146_);
v___x_1191_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v_fst_1180_ = v_val_x3f_1144_;
v_snd_1181_ = v___x_1191_;
goto v___jp_1179_;
}
else
{
lean_object* v_val_1192_; lean_object* v___x_1193_; 
v_val_1192_ = lean_ctor_get(v_val_x3f_1144_, 0);
lean_inc(v_val_1192_);
lean_dec_ref_known(v_val_x3f_1144_, 1);
v___x_1193_ = l_Lean_Elab_Tactic_Do_countUses(v_val_1192_, v_subst_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___f_1195_; lean_object* v___x_1196_; lean_object* v_fst_1197_; lean_object* v_snd_1198_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
v___f_1195_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4));
v___x_1196_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1195_, v_a_1194_);
v_fst_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_fst_1197_);
v_snd_1198_ = lean_ctor_get(v___x_1196_, 1);
lean_inc(v_snd_1198_);
lean_dec_ref(v___x_1196_);
v_fst_1180_ = v_fst_1197_;
v_snd_1181_ = v_snd_1198_;
goto v___jp_1179_;
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_del_object(v___x_1160_);
lean_dec(v_snd_1158_);
lean_dec(v_fst_1157_);
lean_del_object(v___x_1155_);
lean_dec_ref(v_bodyUses_1145_);
v_a_1199_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1193_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1193_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
v___jp_1162_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1166_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_1165_, v_fvarId_1142_);
v___x_1167_ = lean_box(0);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1169_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1164_);
v___x_1170_ = l_Lean_KVMap_setNat(v___x_1167_, v___x_1168_, v___x_1169_);
v___x_1171_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1170_, v_fst_1157_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___x_1166_);
lean_ctor_set(v___x_1160_, 0, v___y_1163_);
v___x_1173_ = v___x_1160_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___y_1163_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1166_);
v___x_1173_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1171_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1174_);
v___x_1176_ = v___x_1155_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
v___jp_1179_:
{
uint8_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1182_ = 0;
v___x_1183_ = lean_box(v___x_1182_);
v___x_1184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_1145_, v_fvarId_1142_, v___x_1183_);
lean_dec(v___x_1183_);
v___x_1185_ = lean_unbox(v___x_1184_);
v___x_1186_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_1185_, v___x_1182_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1187_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_1145_, v_snd_1158_);
lean_dec_ref(v_bodyUses_1145_);
v___x_1188_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_1187_, v_snd_1181_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = lean_unbox(v___x_1184_);
lean_dec(v___x_1184_);
v___y_1163_ = v_fst_1180_;
v___y_1164_ = v___x_1189_;
v___y_1165_ = v___x_1188_;
goto v___jp_1162_;
}
else
{
uint8_t v___x_1190_; 
lean_dec_ref(v_snd_1181_);
lean_dec(v_snd_1158_);
v___x_1190_ = lean_unbox(v___x_1184_);
lean_dec(v___x_1184_);
v___y_1163_ = v_fst_1180_;
v___y_1164_ = v___x_1190_;
v___y_1165_ = v_bodyUses_1145_;
goto v___jp_1162_;
}
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v_subst_1146_);
lean_dec_ref(v_bodyUses_1145_);
lean_dec(v_val_x3f_1144_);
v_a_1209_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1152_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1152_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object* v_fvarId_1217_, lean_object* v_ty_1218_, lean_object* v_val_x3f_1219_, lean_object* v_bodyUses_1220_, lean_object* v_subst_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1217_, v_ty_1218_, v_val_x3f_1219_, v_bodyUses_1220_, v_subst_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_fvarId_1217_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object* v_e_1228_, lean_object* v_subst_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Elab_Tactic_Do_countUses(v_e_1228_, v_subst_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object* v_00_u03b2_1236_, lean_object* v_m_1237_, lean_object* v_a_1238_, lean_object* v_fallback_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_1237_, v_a_1238_, v_fallback_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object* v_00_u03b2_1241_, lean_object* v_m_1242_, lean_object* v_a_1243_, lean_object* v_fallback_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_1241_, v_m_1242_, v_a_1243_, v_fallback_1244_);
lean_dec(v_fallback_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_m_1242_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object* v_00_u03b2_1246_, lean_object* v_m_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_1247_, v_a_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object* v_00_u03b2_1250_, lean_object* v_m_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(v_00_u03b2_1250_, v_m_1251_, v_a_1252_);
lean_dec(v_a_1252_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object* v_00_u03b1_1254_, lean_object* v_msg_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object* v_00_u03b1_1262_, lean_object* v_msg_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(v_00_u03b1_1262_, v_msg_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object* v_00_u03b2_1270_, lean_object* v_m_1271_, lean_object* v_a_1272_, lean_object* v_b_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_1271_, v_a_1272_, v_b_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object* v_00_u03b2_1287_, lean_object* v_a_1288_, lean_object* v_fallback_1289_, lean_object* v_x_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_1288_, v_fallback_1289_, v_x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1292_, lean_object* v_a_1293_, lean_object* v_fallback_1294_, lean_object* v_x_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_1292_, v_a_1293_, v_fallback_1294_, v_x_1295_);
lean_dec(v_x_1295_);
lean_dec(v_fallback_1294_);
lean_dec(v_a_1293_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object* v_00_u03b2_1297_, lean_object* v_a_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_1298_, v_x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1301_, lean_object* v_a_1302_, lean_object* v_x_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_1301_, v_a_1302_, v_x_1303_);
lean_dec(v_a_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object* v_00_u03b2_1305_, lean_object* v_a_1306_, lean_object* v_b_1307_, lean_object* v_x_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_1306_, v_b_1307_, v_x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object* v_as_1312_, size_t v_i_1313_, size_t v_stop_1314_, lean_object* v_b_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_usize_dec_eq(v_i_1313_, v_stop_1314_);
if (v___x_1321_ == 0)
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((size_t)1ULL);
v___x_1323_ = lean_usize_sub(v_i_1313_, v___x_1322_);
v___x_1324_ = lean_array_uget_borrowed(v_as_1312_, v___x_1323_);
if (lean_obj_tag(v___x_1324_) == 0)
{
v_i_1313_ = v___x_1323_;
goto _start;
}
else
{
lean_object* v_val_1326_; lean_object* v_fst_1327_; lean_object* v_snd_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_val_1326_ = lean_ctor_get(v___x_1324_, 0);
v_fst_1327_ = lean_ctor_get(v_b_1315_, 0);
lean_inc(v_fst_1327_);
v_snd_1328_ = lean_ctor_get(v_b_1315_, 1);
lean_inc(v_snd_1328_);
lean_dec_ref(v_b_1315_);
v___x_1329_ = l_Lean_LocalDecl_fvarId(v_val_1326_);
v___x_1330_ = l_Lean_LocalDecl_type(v_val_1326_);
v___x_1331_ = l_Lean_LocalDecl_value_x3f(v_val_1326_, v___x_1321_);
v___x_1332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_1333_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v___x_1329_, v___x_1330_, v___x_1331_, v_snd_1328_, v___x_1332_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___x_1329_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v_snd_1335_; lean_object* v_fst_1336_; lean_object* v_fst_1337_; lean_object* v_snd_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1353_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v_snd_1335_ = lean_ctor_get(v_a_1334_, 1);
lean_inc(v_snd_1335_);
v_fst_1336_ = lean_ctor_get(v_a_1334_, 0);
lean_inc(v_fst_1336_);
lean_dec(v_a_1334_);
v_fst_1337_ = lean_ctor_get(v_snd_1335_, 0);
v_snd_1338_ = lean_ctor_get(v_snd_1335_, 1);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_snd_1335_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1340_ = v_snd_1335_;
v_isShared_1341_ = v_isSharedCheck_1353_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_snd_1338_);
lean_inc(v_fst_1337_);
lean_dec(v_snd_1335_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1353_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___y_1343_; 
if (lean_obj_tag(v_fst_1337_) == 0)
{
lean_object* v___x_1349_; 
lean_inc(v_val_1326_);
v___x_1349_ = l_Lean_LocalDecl_setType(v_val_1326_, v_fst_1336_);
v___y_1343_ = v___x_1349_;
goto v___jp_1342_;
}
else
{
lean_object* v_val_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_val_1350_ = lean_ctor_get(v_fst_1337_, 0);
lean_inc(v_val_1350_);
lean_dec_ref_known(v_fst_1337_, 1);
lean_inc(v_val_1326_);
v___x_1351_ = l_Lean_LocalDecl_setType(v_val_1326_, v_fst_1336_);
v___x_1352_ = l_Lean_LocalDecl_setValue(v___x_1351_, v_val_1350_);
v___y_1343_ = v___x_1352_;
goto v___jp_1342_;
}
v___jp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = lean_array_push(v_fst_1327_, v___y_1343_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1344_);
v___x_1346_ = v___x_1340_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_snd_1338_);
v___x_1346_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
v_i_1313_ = v___x_1323_;
v_b_1315_ = v___x_1346_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_fst_1327_);
v_a_1354_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1333_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1333_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
else
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_b_1315_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1363_, lean_object* v_i_1364_, lean_object* v_stop_1365_, lean_object* v_b_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
size_t v_i_boxed_1372_; size_t v_stop_boxed_1373_; lean_object* v_res_1374_; 
v_i_boxed_1372_ = lean_unbox_usize(v_i_1364_);
lean_dec(v_i_1364_);
v_stop_boxed_1373_ = lean_unbox_usize(v_stop_1365_);
lean_dec(v_stop_1365_);
v_res_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1363_, v_i_boxed_1372_, v_stop_boxed_1373_, v_b_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec_ref(v_as_1363_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object* v_x_1375_, lean_object* v_x_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
if (lean_obj_tag(v_x_1375_) == 0)
{
lean_object* v_cs_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1395_; 
v_cs_1382_ = lean_ctor_get(v_x_1375_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_x_1375_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1384_ = v_x_1375_;
v_isShared_1385_ = v_isSharedCheck_1395_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_cs_1382_);
lean_dec(v_x_1375_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1395_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1386_ = lean_array_get_size(v_cs_1382_);
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_nat_dec_lt(v___x_1387_, v___x_1386_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1390_; 
lean_dec_ref(v_cs_1382_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v_x_1376_);
v___x_1390_ = v___x_1384_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_x_1376_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
size_t v___x_1392_; size_t v___x_1393_; lean_object* v___x_1394_; 
lean_del_object(v___x_1384_);
v___x_1392_ = lean_usize_of_nat(v___x_1386_);
v___x_1393_ = ((size_t)0ULL);
v___x_1394_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_1382_, v___x_1392_, v___x_1393_, v_x_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec_ref(v_cs_1382_);
return v___x_1394_;
}
}
}
else
{
lean_object* v_vs_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1409_; 
v_vs_1396_ = lean_ctor_get(v_x_1375_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_x_1375_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1398_ = v_x_1375_;
v_isShared_1399_ = v_isSharedCheck_1409_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_vs_1396_);
lean_dec(v_x_1375_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1409_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1400_ = lean_array_get_size(v_vs_1396_);
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = lean_nat_dec_lt(v___x_1401_, v___x_1400_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1404_; 
lean_dec_ref(v_vs_1396_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set_tag(v___x_1398_, 0);
lean_ctor_set(v___x_1398_, 0, v_x_1376_);
v___x_1404_ = v___x_1398_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_x_1376_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
else
{
size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
lean_del_object(v___x_1398_);
v___x_1406_ = lean_usize_of_nat(v___x_1400_);
v___x_1407_ = ((size_t)0ULL);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_1396_, v___x_1406_, v___x_1407_, v_x_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec_ref(v_vs_1396_);
return v___x_1408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_1410_, size_t v_i_1411_, size_t v_stop_1412_, lean_object* v_b_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_usize_dec_eq(v_i_1411_, v_stop_1412_);
if (v___x_1419_ == 0)
{
size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_sub(v_i_1411_, v___x_1420_);
v___x_1422_ = lean_array_uget_borrowed(v_as_1410_, v___x_1421_);
lean_inc(v___x_1422_);
v___x_1423_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_1422_, v_b_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v_i_1411_ = v___x_1421_;
v_b_1413_ = v_a_1424_;
goto _start;
}
else
{
return v___x_1423_;
}
}
else
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_b_1413_);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1427_, lean_object* v_i_1428_, lean_object* v_stop_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
size_t v_i_boxed_1436_; size_t v_stop_boxed_1437_; lean_object* v_res_1438_; 
v_i_boxed_1436_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_stop_boxed_1437_ = lean_unbox_usize(v_stop_1429_);
lean_dec(v_stop_1429_);
v_res_1438_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1427_, v_i_boxed_1436_, v_stop_boxed_1437_, v_b_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec_ref(v_as_1427_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1439_, v_x_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object* v_t_1447_, lean_object* v_init_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_root_1454_; lean_object* v_tail_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v_root_1454_ = lean_ctor_get(v_t_1447_, 0);
lean_inc_ref(v_root_1454_);
v_tail_1455_ = lean_ctor_get(v_t_1447_, 1);
lean_inc_ref(v_tail_1455_);
lean_dec_ref(v_t_1447_);
v___x_1456_ = lean_array_get_size(v_tail_1455_);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_nat_dec_lt(v___x_1457_, v___x_1456_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
lean_dec_ref(v_tail_1455_);
v___x_1459_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1454_, v_init_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1459_;
}
else
{
size_t v___x_1460_; size_t v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = lean_usize_of_nat(v___x_1456_);
v___x_1461_ = ((size_t)0ULL);
v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_1455_, v___x_1460_, v___x_1461_, v_init_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec_ref(v_tail_1455_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1454_, v_a_1463_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1464_;
}
else
{
lean_dec_ref(v_root_1454_);
return v___x_1462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object* v_t_1465_, lean_object* v_init_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1465_, v_init_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object* v_lctx_1473_, lean_object* v_init_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_decls_1480_; lean_object* v___x_1481_; 
v_decls_1480_ = lean_ctor_get(v_lctx_1473_, 1);
lean_inc_ref(v_decls_1480_);
lean_dec_ref(v_lctx_1473_);
v___x_1481_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_1480_, v_init_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object* v_lctx_1482_, lean_object* v_init_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1482_, v_init_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t v_sz_1490_, size_t v_i_1491_, lean_object* v_bs_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_usize_dec_lt(v_i_1491_, v_sz_1490_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_bs_1492_);
return v___x_1496_;
}
else
{
lean_object* v_v_1497_; lean_object* v___x_1498_; lean_object* v_bs_x27_1499_; lean_object* v_a_1501_; 
v_v_1497_ = lean_array_uget(v_bs_1492_, v_i_1491_);
v___x_1498_ = lean_unsigned_to_nat(0u);
v_bs_x27_1499_ = lean_array_uset(v_bs_1492_, v_i_1491_, v___x_1498_);
if (lean_obj_tag(v_v_1497_) == 0)
{
v_a_1501_ = v_v_1497_;
goto v___jp_1500_;
}
else
{
lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1520_; 
v_isSharedCheck_1520_ = !lean_is_exclusive(v_v_1497_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; 
v_unused_1521_ = lean_ctor_get(v_v_1497_, 0);
lean_dec(v_unused_1521_);
v___x_1507_ = v_v_1497_;
v_isShared_1508_ = v_isSharedCheck_1520_;
goto v_resetjp_1506_;
}
else
{
lean_dec(v_v_1497_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1520_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1509_ = lean_st_ref_take(v___y_1493_);
v___x_1510_ = l_Lean_instInhabitedLocalDecl_default;
v___x_1511_ = lean_array_get_size(v___x_1509_);
v___x_1512_ = lean_unsigned_to_nat(1u);
v___x_1513_ = lean_nat_sub(v___x_1511_, v___x_1512_);
v___x_1514_ = lean_array_get(v___x_1510_, v___x_1509_, v___x_1513_);
lean_dec(v___x_1513_);
v___x_1515_ = lean_array_pop(v___x_1509_);
v___x_1516_ = lean_st_ref_put(v___y_1493_, v___x_1515_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1514_);
v___x_1518_ = v___x_1507_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1514_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
v_a_1501_ = v___x_1518_;
goto v___jp_1500_;
}
}
}
v___jp_1500_:
{
size_t v___x_1502_; size_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = ((size_t)1ULL);
v___x_1503_ = lean_usize_add(v_i_1491_, v___x_1502_);
v___x_1504_ = lean_array_uset(v_bs_x27_1499_, v_i_1491_, v_a_1501_);
v_i_1491_ = v___x_1503_;
v_bs_1492_ = v___x_1504_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object* v_sz_1522_, lean_object* v_i_1523_, lean_object* v_bs_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
size_t v_sz_boxed_1527_; size_t v_i_boxed_1528_; lean_object* v_res_1529_; 
v_sz_boxed_1527_ = lean_unbox_usize(v_sz_1522_);
lean_dec(v_sz_1522_);
v_i_boxed_1528_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_res_1529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_1527_, v_i_boxed_1528_, v_bs_1524_, v___y_1525_);
lean_dec(v___y_1525_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object* v_x_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
if (lean_obj_tag(v_x_1530_) == 0)
{
lean_object* v_cs_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1563_; 
v_cs_1537_ = lean_ctor_get(v_x_1530_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_x_1530_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1539_ = v_x_1530_;
v_isShared_1540_ = v_isSharedCheck_1563_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_cs_1537_);
lean_dec(v_x_1530_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1563_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
size_t v_sz_1541_; size_t v___x_1542_; lean_object* v___x_1543_; 
v_sz_1541_ = lean_array_size(v_cs_1537_);
v___x_1542_ = ((size_t)0ULL);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1541_, v___x_1542_, v_cs_1537_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1554_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1554_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1554_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v_a_1544_);
v___x_1549_ = v___x_1539_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1549_);
v___x_1551_ = v___x_1546_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_del_object(v___x_1539_);
v_a_1555_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1543_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1543_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
else
{
lean_object* v_vs_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1590_; 
v_vs_1564_ = lean_ctor_get(v_x_1530_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_x_1530_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1566_ = v_x_1530_;
v_isShared_1567_ = v_isSharedCheck_1590_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_vs_1564_);
lean_dec(v_x_1530_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1590_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
size_t v_sz_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
v_sz_1568_ = lean_array_size(v_vs_1564_);
v___x_1569_ = ((size_t)0ULL);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1568_, v___x_1569_, v_vs_1564_, v___y_1531_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1581_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1581_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1581_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v_a_1571_);
v___x_1576_ = v___x_1566_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1576_);
v___x_1578_ = v___x_1573_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_del_object(v___x_1566_);
v_a_1582_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1570_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1570_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t v_sz_1591_, size_t v_i_1592_, lean_object* v_bs_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_usize_dec_lt(v_i_1592_, v_sz_1591_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_bs_1593_);
return v___x_1601_;
}
else
{
lean_object* v_v_1602_; lean_object* v___x_1603_; 
v_v_1602_ = lean_array_uget_borrowed(v_bs_1593_, v_i_1592_);
lean_inc(v_v_1602_);
v___x_1603_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_1602_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; lean_object* v_bs_x27_1606_; size_t v___x_1607_; size_t v___x_1608_; lean_object* v___x_1609_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1605_ = lean_unsigned_to_nat(0u);
v_bs_x27_1606_ = lean_array_uset(v_bs_1593_, v_i_1592_, v___x_1605_);
v___x_1607_ = ((size_t)1ULL);
v___x_1608_ = lean_usize_add(v_i_1592_, v___x_1607_);
v___x_1609_ = lean_array_uset(v_bs_x27_1606_, v_i_1592_, v_a_1604_);
v_i_1592_ = v___x_1608_;
v_bs_1593_ = v___x_1609_;
goto _start;
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v_bs_1593_);
v_a_1611_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1603_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1603_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_1619_, lean_object* v_i_1620_, lean_object* v_bs_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
size_t v_sz_boxed_1628_; size_t v_i_boxed_1629_; lean_object* v_res_1630_; 
v_sz_boxed_1628_ = lean_unbox_usize(v_sz_1619_);
lean_dec(v_sz_1619_);
v_i_boxed_1629_ = lean_unbox_usize(v_i_1620_);
lean_dec(v_i_1620_);
v_res_1630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_1628_, v_i_boxed_1629_, v_bs_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object* v_x_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object* v_t_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_root_1646_; lean_object* v_tail_1647_; lean_object* v_size_1648_; size_t v_shift_1649_; lean_object* v_tailOff_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1686_; 
v_root_1646_ = lean_ctor_get(v_t_1639_, 0);
v_tail_1647_ = lean_ctor_get(v_t_1639_, 1);
v_size_1648_ = lean_ctor_get(v_t_1639_, 2);
v_shift_1649_ = lean_ctor_get_usize(v_t_1639_, 4);
v_tailOff_1650_ = lean_ctor_get(v_t_1639_, 3);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_t_1639_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1652_ = v_t_1639_;
v_isShared_1653_ = v_isSharedCheck_1686_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_tailOff_1650_);
lean_inc(v_size_1648_);
lean_inc(v_tail_1647_);
lean_inc(v_root_1646_);
lean_dec(v_t_1639_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1686_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_1646_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; size_t v_sz_1656_; size_t v___x_1657_; lean_object* v___x_1658_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v_sz_1656_ = lean_array_size(v_tail_1647_);
v___x_1657_ = ((size_t)0ULL);
v___x_1658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1656_, v___x_1657_, v_tail_1647_, v___y_1640_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1669_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 1, v_a_1659_);
lean_ctor_set(v___x_1652_, 0, v_a_1655_);
v___x_1664_ = v___x_1652_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1655_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_a_1659_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_size_1648_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v_tailOff_1650_);
lean_ctor_set_usize(v_reuseFailAlloc_1668_, 4, v_shift_1649_);
v___x_1664_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1664_);
v___x_1666_ = v___x_1661_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_a_1655_);
lean_del_object(v___x_1652_);
lean_dec(v_tailOff_1650_);
lean_dec(v_size_1648_);
v_a_1670_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1658_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1658_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_del_object(v___x_1652_);
lean_dec(v_tailOff_1650_);
lean_dec(v_size_1648_);
lean_dec_ref(v_tail_1647_);
v_a_1678_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1654_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1654_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object* v_t_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object* v_ctx_1695_, lean_object* v_targetUses_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_decls_1702_; lean_object* v_fvarIdToDecl_1703_; lean_object* v_auxDeclToFullName_1704_; lean_object* v_size_1705_; lean_object* v_decls_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_decls_1702_ = lean_ctor_get(v_ctx_1695_, 1);
lean_inc_ref(v_decls_1702_);
v_fvarIdToDecl_1703_ = lean_ctor_get(v_ctx_1695_, 0);
lean_inc_ref(v_fvarIdToDecl_1703_);
v_auxDeclToFullName_1704_ = lean_ctor_get(v_ctx_1695_, 2);
lean_inc(v_auxDeclToFullName_1704_);
v_size_1705_ = lean_ctor_get(v_decls_1702_, 2);
v_decls_1706_ = lean_mk_empty_array_with_capacity(v_size_1705_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v_decls_1706_);
lean_ctor_set(v___x_1707_, 1, v_targetUses_1696_);
v___x_1708_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_ctx_1695_, v___x_1707_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v_fst_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v_fst_1710_ = lean_ctor_get(v_a_1709_, 0);
lean_inc(v_fst_1710_);
lean_dec(v_a_1709_);
v___x_1711_ = lean_st_mk_ref(v_fst_1710_);
v___x_1712_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_1702_, v___x_1711_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1722_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1717_ = lean_st_ref_get(v___x_1711_);
lean_dec(v___x_1711_);
lean_dec(v___x_1717_);
v___x_1718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1718_, 0, v_fvarIdToDecl_1703_);
lean_ctor_set(v___x_1718_, 1, v_a_1713_);
lean_ctor_set(v___x_1718_, 2, v_auxDeclToFullName_1704_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1718_);
v___x_1720_ = v___x_1715_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v___x_1711_);
lean_dec(v_auxDeclToFullName_1704_);
lean_dec_ref(v_fvarIdToDecl_1703_);
v_a_1723_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1712_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1712_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_auxDeclToFullName_1704_);
lean_dec_ref(v_fvarIdToDecl_1703_);
lean_dec_ref(v_decls_1702_);
v_a_1731_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1708_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1708_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object* v_ctx_1739_, lean_object* v_targetUses_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1739_, v_targetUses_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t v_sz_1747_, size_t v_i_1748_, lean_object* v_bs_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1747_, v_i_1748_, v_bs_1749_, v___y_1750_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object* v_sz_1757_, lean_object* v_i_1758_, lean_object* v_bs_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
size_t v_sz_boxed_1766_; size_t v_i_boxed_1767_; lean_object* v_res_1768_; 
v_sz_boxed_1766_ = lean_unbox_usize(v_sz_1757_);
lean_dec(v_sz_1757_);
v_i_boxed_1767_ = lean_unbox_usize(v_i_1758_);
lean_dec(v_i_1758_);
v_res_1768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_1766_, v_i_boxed_1767_, v_bs_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
return v_res_1768_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t v_u_1769_, lean_object* v_rhs_1770_, uint8_t v_elimTrivial_1771_){
_start:
{
uint8_t v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = 2;
v___x_1773_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_1769_, v___x_1772_);
if (v___x_1773_ == 0)
{
return v___x_1773_;
}
else
{
if (v_elimTrivial_1771_ == 0)
{
return v___x_1773_;
}
else
{
uint8_t v___x_1774_; 
v___x_1774_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_1770_);
if (v___x_1774_ == 0)
{
return v___x_1773_;
}
else
{
uint8_t v___x_1775_; 
v___x_1775_ = 0;
return v___x_1775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object* v_u_1776_, lean_object* v_rhs_1777_, lean_object* v_elimTrivial_1778_){
_start:
{
uint8_t v_u_boxed_1779_; uint8_t v_elimTrivial_boxed_1780_; uint8_t v_res_1781_; lean_object* v_r_1782_; 
v_u_boxed_1779_ = lean_unbox(v_u_1776_);
v_elimTrivial_boxed_1780_ = lean_unbox(v_elimTrivial_1778_);
v_res_1781_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_1779_, v_rhs_1777_, v_elimTrivial_boxed_1780_);
lean_dec_ref(v_rhs_1777_);
v_r_1782_ = lean_box(v_res_1781_);
return v_r_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t v_elimTrivial_1785_, lean_object* v_e_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
if (lean_obj_tag(v_e_1786_) == 8)
{
lean_object* v_type_1793_; 
v_type_1793_ = lean_ctor_get(v_e_1786_, 1);
if (lean_obj_tag(v_type_1793_) == 10)
{
lean_object* v_value_1794_; lean_object* v_body_1795_; lean_object* v_data_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v_uses_1800_; uint8_t v___x_1801_; 
v_value_1794_ = lean_ctor_get(v_e_1786_, 2);
v_body_1795_ = lean_ctor_get(v_e_1786_, 3);
v_data_1796_ = lean_ctor_get(v_type_1793_, 0);
v___x_1797_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1798_ = lean_unsigned_to_nat(2u);
v___x_1799_ = l_Lean_KVMap_getNat(v_data_1796_, v___x_1797_, v___x_1798_);
v_uses_1800_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_1799_);
lean_dec(v___x_1799_);
v___x_1801_ = l_Lean_Elab_Tactic_Do_doNotDup(v_uses_1800_, v_value_1794_, v_elimTrivial_1785_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_expr_instantiate1(v_body_1795_, v_value_1794_);
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object* v_elimTrivial_1811_, lean_object* v_e_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
uint8_t v_elimTrivial_boxed_1819_; lean_object* v_res_1820_; 
v_elimTrivial_boxed_1819_ = lean_unbox(v_elimTrivial_1811_);
v_res_1820_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_boxed_1819_, v_e_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v_e_1812_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object* v_e_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v_e_1821_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object* v_e_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
return v_res_1837_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = l_Lean_maxRecDepthErrorMessage;
v___x_1844_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_1846_ = l_Lean_MessageData_ofFormat(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_1848_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_1849_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v___x_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_1850_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v_ref_1850_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1855_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object* v_x_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___y_1867_; lean_object* v_fileName_1876_; lean_object* v_fileMap_1877_; lean_object* v_options_1878_; lean_object* v_currRecDepth_1879_; lean_object* v_maxRecDepth_1880_; lean_object* v_ref_1881_; lean_object* v_currNamespace_1882_; lean_object* v_openDecls_1883_; lean_object* v_initHeartbeats_1884_; lean_object* v_maxHeartbeats_1885_; lean_object* v_quotContext_1886_; lean_object* v_currMacroScope_1887_; uint8_t v_diag_1888_; lean_object* v_cancelTk_x3f_1889_; uint8_t v_suppressElabErrors_1890_; lean_object* v_inheritedTraceOptions_1891_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v_fileName_1876_ = lean_ctor_get(v___y_1863_, 0);
v_fileMap_1877_ = lean_ctor_get(v___y_1863_, 1);
v_options_1878_ = lean_ctor_get(v___y_1863_, 2);
v_currRecDepth_1879_ = lean_ctor_get(v___y_1863_, 3);
v_maxRecDepth_1880_ = lean_ctor_get(v___y_1863_, 4);
v_ref_1881_ = lean_ctor_get(v___y_1863_, 5);
v_currNamespace_1882_ = lean_ctor_get(v___y_1863_, 6);
v_openDecls_1883_ = lean_ctor_get(v___y_1863_, 7);
v_initHeartbeats_1884_ = lean_ctor_get(v___y_1863_, 8);
v_maxHeartbeats_1885_ = lean_ctor_get(v___y_1863_, 9);
v_quotContext_1886_ = lean_ctor_get(v___y_1863_, 10);
v_currMacroScope_1887_ = lean_ctor_get(v___y_1863_, 11);
v_diag_1888_ = lean_ctor_get_uint8(v___y_1863_, sizeof(void*)*14);
v_cancelTk_x3f_1889_ = lean_ctor_get(v___y_1863_, 12);
v_suppressElabErrors_1890_ = lean_ctor_get_uint8(v___y_1863_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1891_ = lean_ctor_get(v___y_1863_, 13);
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = lean_nat_dec_eq(v_maxRecDepth_1880_, v___x_1897_);
if (v___x_1898_ == 0)
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_nat_dec_eq(v_currRecDepth_1879_, v_maxRecDepth_1880_);
if (v___x_1899_ == 0)
{
goto v___jp_1892_;
}
else
{
lean_object* v___x_1900_; 
lean_dec_ref(v_x_1858_);
lean_inc(v_ref_1881_);
v___x_1900_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1881_);
v___y_1867_ = v___x_1900_;
goto v___jp_1866_;
}
}
else
{
goto v___jp_1892_;
}
v___jp_1866_:
{
if (lean_obj_tag(v___y_1867_) == 0)
{
return v___y_1867_;
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1868_ = lean_ctor_get(v___y_1867_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___y_1867_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___y_1867_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___y_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
v___jp_1892_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1893_ = lean_unsigned_to_nat(1u);
v___x_1894_ = lean_nat_add(v_currRecDepth_1879_, v___x_1893_);
lean_inc_ref(v_inheritedTraceOptions_1891_);
lean_inc(v_cancelTk_x3f_1889_);
lean_inc(v_currMacroScope_1887_);
lean_inc(v_quotContext_1886_);
lean_inc(v_maxHeartbeats_1885_);
lean_inc(v_initHeartbeats_1884_);
lean_inc(v_openDecls_1883_);
lean_inc(v_currNamespace_1882_);
lean_inc(v_ref_1881_);
lean_inc(v_maxRecDepth_1880_);
lean_inc_ref(v_options_1878_);
lean_inc_ref(v_fileMap_1877_);
lean_inc_ref(v_fileName_1876_);
v___x_1895_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1895_, 0, v_fileName_1876_);
lean_ctor_set(v___x_1895_, 1, v_fileMap_1877_);
lean_ctor_set(v___x_1895_, 2, v_options_1878_);
lean_ctor_set(v___x_1895_, 3, v___x_1894_);
lean_ctor_set(v___x_1895_, 4, v_maxRecDepth_1880_);
lean_ctor_set(v___x_1895_, 5, v_ref_1881_);
lean_ctor_set(v___x_1895_, 6, v_currNamespace_1882_);
lean_ctor_set(v___x_1895_, 7, v_openDecls_1883_);
lean_ctor_set(v___x_1895_, 8, v_initHeartbeats_1884_);
lean_ctor_set(v___x_1895_, 9, v_maxHeartbeats_1885_);
lean_ctor_set(v___x_1895_, 10, v_quotContext_1886_);
lean_ctor_set(v___x_1895_, 11, v_currMacroScope_1887_);
lean_ctor_set(v___x_1895_, 12, v_cancelTk_x3f_1889_);
lean_ctor_set(v___x_1895_, 13, v_inheritedTraceOptions_1891_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*14, v_diag_1888_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*14 + 1, v_suppressElabErrors_1890_);
lean_inc(v___y_1864_);
lean_inc(v___y_1862_);
lean_inc_ref(v___y_1861_);
lean_inc(v___y_1860_);
lean_inc(v___y_1859_);
v___x_1896_ = lean_apply_7(v_x_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___x_1895_, v___y_1864_, lean_box(0));
v___y_1867_ = v___x_1896_;
goto v___jp_1866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec(v___y_1902_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_1910_, lean_object* v_x_1911_){
_start:
{
if (lean_obj_tag(v_x_1911_) == 0)
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_box(0);
return v___x_1912_;
}
else
{
lean_object* v_key_1913_; lean_object* v_value_1914_; lean_object* v_tail_1915_; uint8_t v___x_1916_; 
v_key_1913_ = lean_ctor_get(v_x_1911_, 0);
v_value_1914_ = lean_ctor_get(v_x_1911_, 1);
v_tail_1915_ = lean_ctor_get(v_x_1911_, 2);
v___x_1916_ = l_Lean_ExprStructEq_beq(v_key_1913_, v_a_1910_);
if (v___x_1916_ == 0)
{
v_x_1911_ = v_tail_1915_;
goto _start;
}
else
{
lean_object* v___x_1918_; 
lean_inc(v_value_1914_);
v___x_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_value_1914_);
return v___x_1918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_1919_, lean_object* v_x_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1919_, v_x_1920_);
lean_dec(v_x_1920_);
lean_dec_ref(v_a_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_m_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_buckets_1924_; lean_object* v___x_1925_; uint64_t v___x_1926_; uint64_t v___x_1927_; uint64_t v___x_1928_; uint64_t v_fold_1929_; uint64_t v___x_1930_; uint64_t v___x_1931_; uint64_t v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; size_t v___x_1936_; size_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_buckets_1924_ = lean_ctor_get(v_m_1922_, 1);
v___x_1925_ = lean_array_get_size(v_buckets_1924_);
v___x_1926_ = l_Lean_ExprStructEq_hash(v_a_1923_);
v___x_1927_ = 32ULL;
v___x_1928_ = lean_uint64_shift_right(v___x_1926_, v___x_1927_);
v_fold_1929_ = lean_uint64_xor(v___x_1926_, v___x_1928_);
v___x_1930_ = 16ULL;
v___x_1931_ = lean_uint64_shift_right(v_fold_1929_, v___x_1930_);
v___x_1932_ = lean_uint64_xor(v_fold_1929_, v___x_1931_);
v___x_1933_ = lean_uint64_to_usize(v___x_1932_);
v___x_1934_ = lean_usize_of_nat(v___x_1925_);
v___x_1935_ = ((size_t)1ULL);
v___x_1936_ = lean_usize_sub(v___x_1934_, v___x_1935_);
v___x_1937_ = lean_usize_land(v___x_1933_, v___x_1936_);
v___x_1938_ = lean_array_uget_borrowed(v_buckets_1924_, v___x_1937_);
v___x_1939_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1923_, v___x_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_1940_, v_a_1941_);
lean_dec_ref(v_a_1941_);
lean_dec_ref(v_m_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v_b_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; 
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1945_);
lean_inc(v___y_1944_);
v___x_1952_ = lean_apply_8(v_k_1943_, v_b_1946_, v___y_1944_, v___y_1945_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, lean_box(0));
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v_b_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1953_, v___y_1954_, v___y_1955_, v_b_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_1963_, lean_object* v_type_1964_, lean_object* v_val_1965_, lean_object* v_k_1966_, uint8_t v_nondep_1967_, uint8_t v_kind_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___f_1976_; lean_object* v___x_1977_; 
lean_inc(v___y_1970_);
lean_inc(v___y_1969_);
v___f_1976_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1976_, 0, v_k_1966_);
lean_closure_set(v___f_1976_, 1, v___y_1969_);
lean_closure_set(v___f_1976_, 2, v___y_1970_);
v___x_1977_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1963_, v_type_1964_, v_val_1965_, v___f_1976_, v_nondep_1967_, v_kind_1968_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1977_) == 0)
{
return v___x_1977_;
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_1986_, lean_object* v_type_1987_, lean_object* v_val_1988_, lean_object* v_k_1989_, lean_object* v_nondep_1990_, lean_object* v_kind_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
uint8_t v_nondep_boxed_1999_; uint8_t v_kind_boxed_2000_; lean_object* v_res_2001_; 
v_nondep_boxed_1999_ = lean_unbox(v_nondep_1990_);
v_kind_boxed_2000_ = lean_unbox(v_kind_1991_);
v_res_2001_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1986_, v_type_1987_, v_val_1988_, v_k_1989_, v_nondep_boxed_1999_, v_kind_boxed_2000_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec(v___y_1992_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_2002_, uint8_t v_bi_2003_, lean_object* v_type_2004_, lean_object* v_k_2005_, uint8_t v_kind_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v___f_2014_; lean_object* v___x_2015_; 
lean_inc(v___y_2008_);
lean_inc(v___y_2007_);
v___f_2014_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2014_, 0, v_k_2005_);
lean_closure_set(v___f_2014_, 1, v___y_2007_);
lean_closure_set(v___f_2014_, 2, v___y_2008_);
v___x_2015_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2002_, v_bi_2003_, v_type_2004_, v___f_2014_, v_kind_2006_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
if (lean_obj_tag(v___x_2015_) == 0)
{
return v___x_2015_;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_2024_, lean_object* v_bi_2025_, lean_object* v_type_2026_, lean_object* v_k_2027_, lean_object* v_kind_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
uint8_t v_bi_boxed_2036_; uint8_t v_kind_boxed_2037_; lean_object* v_res_2038_; 
v_bi_boxed_2036_ = lean_unbox(v_bi_2025_);
v_kind_boxed_2037_ = lean_unbox(v_kind_2028_);
v_res_2038_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2024_, v_bi_boxed_2036_, v_type_2026_, v_k_2027_, v_kind_boxed_2037_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec(v___y_2029_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2039_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2055_, lean_object* v_x_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = lean_apply_1(v_x_2056_, lean_box(0));
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2065_, lean_object* v_x_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2065_, v_x_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_2074_, lean_object* v_x_2075_){
_start:
{
if (lean_obj_tag(v_x_2075_) == 0)
{
return v_x_2074_;
}
else
{
lean_object* v_key_2076_; lean_object* v_value_2077_; lean_object* v_tail_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2101_; 
v_key_2076_ = lean_ctor_get(v_x_2075_, 0);
v_value_2077_ = lean_ctor_get(v_x_2075_, 1);
v_tail_2078_ = lean_ctor_get(v_x_2075_, 2);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_x_2075_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2080_ = v_x_2075_;
v_isShared_2081_ = v_isSharedCheck_2101_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_tail_2078_);
lean_inc(v_value_2077_);
lean_inc(v_key_2076_);
lean_dec(v_x_2075_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2101_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; uint64_t v___x_2083_; uint64_t v___x_2084_; uint64_t v___x_2085_; uint64_t v_fold_2086_; uint64_t v___x_2087_; uint64_t v___x_2088_; uint64_t v___x_2089_; size_t v___x_2090_; size_t v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2082_ = lean_array_get_size(v_x_2074_);
v___x_2083_ = l_Lean_ExprStructEq_hash(v_key_2076_);
v___x_2084_ = 32ULL;
v___x_2085_ = lean_uint64_shift_right(v___x_2083_, v___x_2084_);
v_fold_2086_ = lean_uint64_xor(v___x_2083_, v___x_2085_);
v___x_2087_ = 16ULL;
v___x_2088_ = lean_uint64_shift_right(v_fold_2086_, v___x_2087_);
v___x_2089_ = lean_uint64_xor(v_fold_2086_, v___x_2088_);
v___x_2090_ = lean_uint64_to_usize(v___x_2089_);
v___x_2091_ = lean_usize_of_nat(v___x_2082_);
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_sub(v___x_2091_, v___x_2092_);
v___x_2094_ = lean_usize_land(v___x_2090_, v___x_2093_);
v___x_2095_ = lean_array_uget_borrowed(v_x_2074_, v___x_2094_);
lean_inc(v___x_2095_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 2, v___x_2095_);
v___x_2097_ = v___x_2080_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_key_2076_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_value_2077_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_array_uset(v_x_2074_, v___x_2094_, v___x_2097_);
v_x_2074_ = v___x_2098_;
v_x_2075_ = v_tail_2078_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_2102_, lean_object* v_source_2103_, lean_object* v_target_2104_){
_start:
{
lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = lean_array_get_size(v_source_2103_);
v___x_2106_ = lean_nat_dec_lt(v_i_2102_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_dec_ref(v_source_2103_);
lean_dec(v_i_2102_);
return v_target_2104_;
}
else
{
lean_object* v_es_2107_; lean_object* v___x_2108_; lean_object* v_source_2109_; lean_object* v_target_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v_es_2107_ = lean_array_fget(v_source_2103_, v_i_2102_);
v___x_2108_ = lean_box(0);
v_source_2109_ = lean_array_fset(v_source_2103_, v_i_2102_, v___x_2108_);
v_target_2110_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_2104_, v_es_2107_);
v___x_2111_ = lean_unsigned_to_nat(1u);
v___x_2112_ = lean_nat_add(v_i_2102_, v___x_2111_);
lean_dec(v_i_2102_);
v_i_2102_ = v___x_2112_;
v_source_2103_ = v_source_2109_;
v_target_2104_ = v_target_2110_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_2114_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v_nbuckets_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2115_ = lean_array_get_size(v_data_2114_);
v___x_2116_ = lean_unsigned_to_nat(2u);
v_nbuckets_2117_ = lean_nat_mul(v___x_2115_, v___x_2116_);
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = lean_box(0);
v___x_2120_ = lean_mk_array(v_nbuckets_2117_, v___x_2119_);
v___x_2121_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_2118_, v_data_2114_, v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_2122_, lean_object* v_b_2123_, lean_object* v_x_2124_){
_start:
{
if (lean_obj_tag(v_x_2124_) == 0)
{
lean_dec(v_b_2123_);
lean_dec_ref(v_a_2122_);
return v_x_2124_;
}
else
{
lean_object* v_key_2125_; lean_object* v_value_2126_; lean_object* v_tail_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2139_; 
v_key_2125_ = lean_ctor_get(v_x_2124_, 0);
v_value_2126_ = lean_ctor_get(v_x_2124_, 1);
v_tail_2127_ = lean_ctor_get(v_x_2124_, 2);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_x_2124_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2129_ = v_x_2124_;
v_isShared_2130_ = v_isSharedCheck_2139_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_tail_2127_);
lean_inc(v_value_2126_);
lean_inc(v_key_2125_);
lean_dec(v_x_2124_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2139_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
uint8_t v___x_2131_; 
v___x_2131_ = l_Lean_ExprStructEq_beq(v_key_2125_, v_a_2122_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2122_, v_b_2123_, v_tail_2127_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 2, v___x_2132_);
v___x_2134_ = v___x_2129_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_key_2125_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_value_2126_);
lean_ctor_set(v_reuseFailAlloc_2135_, 2, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
else
{
lean_object* v___x_2137_; 
lean_dec(v_value_2126_);
lean_dec(v_key_2125_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v_b_2123_);
lean_ctor_set(v___x_2129_, 0, v_a_2122_);
v___x_2137_ = v___x_2129_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2122_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_b_2123_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_tail_2127_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_2140_, lean_object* v_x_2141_){
_start:
{
if (lean_obj_tag(v_x_2141_) == 0)
{
uint8_t v___x_2142_; 
v___x_2142_ = 0;
return v___x_2142_;
}
else
{
lean_object* v_key_2143_; lean_object* v_tail_2144_; uint8_t v___x_2145_; 
v_key_2143_ = lean_ctor_get(v_x_2141_, 0);
v_tail_2144_ = lean_ctor_get(v_x_2141_, 2);
v___x_2145_ = l_Lean_ExprStructEq_beq(v_key_2143_, v_a_2140_);
if (v___x_2145_ == 0)
{
v_x_2141_ = v_tail_2144_;
goto _start;
}
else
{
return v___x_2145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_2147_, lean_object* v_x_2148_){
_start:
{
uint8_t v_res_2149_; lean_object* v_r_2150_; 
v_res_2149_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2147_, v_x_2148_);
lean_dec(v_x_2148_);
lean_dec_ref(v_a_2147_);
v_r_2150_ = lean_box(v_res_2149_);
return v_r_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2151_, lean_object* v_a_2152_, lean_object* v_b_2153_){
_start:
{
lean_object* v_size_2154_; lean_object* v_buckets_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2198_; 
v_size_2154_ = lean_ctor_get(v_m_2151_, 0);
v_buckets_2155_ = lean_ctor_get(v_m_2151_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_m_2151_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2157_ = v_m_2151_;
v_isShared_2158_ = v_isSharedCheck_2198_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_buckets_2155_);
lean_inc(v_size_2154_);
lean_dec(v_m_2151_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2198_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; uint64_t v___x_2160_; uint64_t v___x_2161_; uint64_t v___x_2162_; uint64_t v_fold_2163_; uint64_t v___x_2164_; uint64_t v___x_2165_; uint64_t v___x_2166_; size_t v___x_2167_; size_t v___x_2168_; size_t v___x_2169_; size_t v___x_2170_; size_t v___x_2171_; lean_object* v_bkt_2172_; uint8_t v___x_2173_; 
v___x_2159_ = lean_array_get_size(v_buckets_2155_);
v___x_2160_ = l_Lean_ExprStructEq_hash(v_a_2152_);
v___x_2161_ = 32ULL;
v___x_2162_ = lean_uint64_shift_right(v___x_2160_, v___x_2161_);
v_fold_2163_ = lean_uint64_xor(v___x_2160_, v___x_2162_);
v___x_2164_ = 16ULL;
v___x_2165_ = lean_uint64_shift_right(v_fold_2163_, v___x_2164_);
v___x_2166_ = lean_uint64_xor(v_fold_2163_, v___x_2165_);
v___x_2167_ = lean_uint64_to_usize(v___x_2166_);
v___x_2168_ = lean_usize_of_nat(v___x_2159_);
v___x_2169_ = ((size_t)1ULL);
v___x_2170_ = lean_usize_sub(v___x_2168_, v___x_2169_);
v___x_2171_ = lean_usize_land(v___x_2167_, v___x_2170_);
v_bkt_2172_ = lean_array_uget_borrowed(v_buckets_2155_, v___x_2171_);
v___x_2173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2152_, v_bkt_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; lean_object* v_size_x27_2175_; lean_object* v___x_2176_; lean_object* v_buckets_x27_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2174_ = lean_unsigned_to_nat(1u);
v_size_x27_2175_ = lean_nat_add(v_size_2154_, v___x_2174_);
lean_dec(v_size_2154_);
lean_inc(v_bkt_2172_);
v___x_2176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2176_, 0, v_a_2152_);
lean_ctor_set(v___x_2176_, 1, v_b_2153_);
lean_ctor_set(v___x_2176_, 2, v_bkt_2172_);
v_buckets_x27_2177_ = lean_array_uset(v_buckets_2155_, v___x_2171_, v___x_2176_);
v___x_2178_ = lean_unsigned_to_nat(4u);
v___x_2179_ = lean_nat_mul(v_size_x27_2175_, v___x_2178_);
v___x_2180_ = lean_unsigned_to_nat(3u);
v___x_2181_ = lean_nat_div(v___x_2179_, v___x_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_array_get_size(v_buckets_x27_2177_);
v___x_2183_ = lean_nat_dec_le(v___x_2181_, v___x_2182_);
lean_dec(v___x_2181_);
if (v___x_2183_ == 0)
{
lean_object* v_val_2184_; lean_object* v___x_2186_; 
v_val_2184_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_2177_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 1, v_val_2184_);
lean_ctor_set(v___x_2157_, 0, v_size_x27_2175_);
v___x_2186_ = v___x_2157_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_size_x27_2175_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_val_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
else
{
lean_object* v___x_2189_; 
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 1, v_buckets_x27_2177_);
lean_ctor_set(v___x_2157_, 0, v_size_x27_2175_);
v___x_2189_ = v___x_2157_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_size_x27_2175_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_buckets_x27_2177_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
else
{
lean_object* v___x_2191_; lean_object* v_buckets_x27_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
lean_inc(v_bkt_2172_);
v___x_2191_ = lean_box(0);
v_buckets_x27_2192_ = lean_array_uset(v_buckets_2155_, v___x_2171_, v___x_2191_);
v___x_2193_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2152_, v_b_2153_, v_bkt_2172_);
v___x_2194_ = lean_array_uset(v_buckets_x27_2192_, v___x_2171_, v___x_2193_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 1, v___x_2194_);
v___x_2196_ = v___x_2157_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_size_2154_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2199_, lean_object* v_e_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2203_ = lean_st_ref_take(v_a_2199_);
v___x_2204_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2203_, v_e_2200_, v_a_2201_);
v___x_2205_ = lean_st_ref_put(v_a_2199_, v___x_2204_);
v___x_2206_ = lean_box(0);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2207_, lean_object* v_e_2208_, lean_object* v_a_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2207_, v_e_2208_, v_a_2209_);
lean_dec(v_a_2207_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_2215_, lean_object* v_pre_2216_, lean_object* v_post_2217_, uint8_t v_usedLetOnly_2218_, uint8_t v_skipConstInApp_2219_, uint8_t v_skipInstances_2220_, lean_object* v_body_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_array_push(v_fvars_2215_, v_x_2222_);
v___x_2231_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2216_, v_post_2217_, v_usedLetOnly_2218_, v_skipConstInApp_2219_, v_skipInstances_2220_, v___x_2230_, v_body_2221_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_2232_, lean_object* v_pre_2233_, lean_object* v_post_2234_, lean_object* v_usedLetOnly_2235_, lean_object* v_skipConstInApp_2236_, lean_object* v_skipInstances_2237_, lean_object* v_body_2238_, lean_object* v_x_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
uint8_t v_usedLetOnly_boxed_2247_; uint8_t v_skipConstInApp_boxed_2248_; uint8_t v_skipInstances_boxed_2249_; lean_object* v_res_2250_; 
v_usedLetOnly_boxed_2247_ = lean_unbox(v_usedLetOnly_2235_);
v_skipConstInApp_boxed_2248_ = lean_unbox(v_skipConstInApp_2236_);
v_skipInstances_boxed_2249_ = lean_unbox(v_skipInstances_2237_);
v_res_2250_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2232_, v_pre_2233_, v_post_2234_, v_usedLetOnly_boxed_2247_, v_skipConstInApp_boxed_2248_, v_skipInstances_boxed_2249_, v_body_2238_, v_x_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec(v___y_2240_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object* v_pre_2251_, lean_object* v_post_2252_, uint8_t v_usedLetOnly_2253_, uint8_t v_skipConstInApp_2254_, uint8_t v_skipInstances_2255_, lean_object* v_e_2256_, lean_object* v_a_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; 
lean_inc_ref(v_post_2252_);
lean_inc(v___y_2262_);
lean_inc_ref(v___y_2261_);
lean_inc(v___y_2260_);
lean_inc_ref(v___y_2259_);
lean_inc(v___y_2258_);
lean_inc_ref(v_e_2256_);
v___x_2264_ = lean_apply_7(v_post_2252_, v_e_2256_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, lean_box(0));
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2283_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2283_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2283_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
switch(lean_obj_tag(v_a_2265_))
{
case 0:
{
lean_object* v_e_2269_; lean_object* v___x_2271_; 
lean_dec_ref(v_e_2256_);
lean_dec_ref(v_post_2252_);
lean_dec_ref(v_pre_2251_);
v_e_2269_ = lean_ctor_get(v_a_2265_, 0);
lean_inc_ref(v_e_2269_);
lean_dec_ref_known(v_a_2265_, 1);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v_e_2269_);
v___x_2271_ = v___x_2267_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_e_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
case 1:
{
lean_object* v_e_2273_; lean_object* v___x_2274_; 
lean_del_object(v___x_2267_);
lean_dec_ref(v_e_2256_);
v_e_2273_ = lean_ctor_get(v_a_2265_, 0);
lean_inc_ref(v_e_2273_);
lean_dec_ref_known(v_a_2265_, 1);
v___x_2274_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2251_, v_post_2252_, v_usedLetOnly_2253_, v_skipConstInApp_2254_, v_skipInstances_2255_, v_e_2273_, v_a_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
return v___x_2274_;
}
default: 
{
lean_object* v_e_x3f_2275_; 
lean_dec_ref(v_post_2252_);
lean_dec_ref(v_pre_2251_);
v_e_x3f_2275_ = lean_ctor_get(v_a_2265_, 0);
lean_inc(v_e_x3f_2275_);
lean_dec_ref_known(v_a_2265_, 1);
if (lean_obj_tag(v_e_x3f_2275_) == 0)
{
lean_object* v___x_2277_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v_e_2256_);
v___x_2277_ = v___x_2267_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_e_2256_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
else
{
lean_object* v_val_2279_; lean_object* v___x_2281_; 
lean_dec_ref(v_e_2256_);
v_val_2279_ = lean_ctor_get(v_e_x3f_2275_, 0);
lean_inc(v_val_2279_);
lean_dec_ref_known(v_e_x3f_2275_, 1);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v_val_2279_);
v___x_2281_ = v___x_2267_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_val_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v_e_2256_);
lean_dec_ref(v_post_2252_);
lean_dec_ref(v_pre_2251_);
v_a_2284_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2264_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2264_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object* v_pre_2292_, lean_object* v_post_2293_, uint8_t v_usedLetOnly_2294_, uint8_t v_skipConstInApp_2295_, uint8_t v_skipInstances_2296_, lean_object* v_fvars_2297_, lean_object* v_e_2298_, lean_object* v_a_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
if (lean_obj_tag(v_e_2298_) == 6)
{
lean_object* v_binderName_2306_; lean_object* v_binderType_2307_; lean_object* v_body_2308_; uint8_t v_binderInfo_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_binderName_2306_ = lean_ctor_get(v_e_2298_, 0);
lean_inc(v_binderName_2306_);
v_binderType_2307_ = lean_ctor_get(v_e_2298_, 1);
lean_inc_ref(v_binderType_2307_);
v_body_2308_ = lean_ctor_get(v_e_2298_, 2);
lean_inc_ref(v_body_2308_);
v_binderInfo_2309_ = lean_ctor_get_uint8(v_e_2298_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2298_, 3);
v___x_2310_ = lean_expr_instantiate_rev(v_binderType_2307_, v_fvars_2297_);
lean_dec_ref(v_binderType_2307_);
lean_inc_ref(v_post_2293_);
lean_inc_ref(v_pre_2292_);
v___x_2311_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2292_, v_post_2293_, v_usedLetOnly_2294_, v_skipConstInApp_2295_, v_skipInstances_2296_, v___x_2310_, v_a_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___f_2316_; uint8_t v___x_2317_; lean_object* v___x_2318_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = lean_box(v_usedLetOnly_2294_);
v___x_2314_ = lean_box(v_skipConstInApp_2295_);
v___x_2315_ = lean_box(v_skipInstances_2296_);
v___f_2316_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2316_, 0, v_fvars_2297_);
lean_closure_set(v___f_2316_, 1, v_pre_2292_);
lean_closure_set(v___f_2316_, 2, v_post_2293_);
lean_closure_set(v___f_2316_, 3, v___x_2313_);
lean_closure_set(v___f_2316_, 4, v___x_2314_);
lean_closure_set(v___f_2316_, 5, v___x_2315_);
lean_closure_set(v___f_2316_, 6, v_body_2308_);
v___x_2317_ = 0;
v___x_2318_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2306_, v_binderInfo_2309_, v_a_2312_, v___f_2316_, v___x_2317_, v_a_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
return v___x_2318_;
}
else
{
lean_dec_ref(v_body_2308_);
lean_dec(v_binderName_2306_);
lean_dec_ref(v_fvars_2297_);
lean_dec_ref(v_post_2293_);
lean_dec_ref(v_pre_2292_);
return v___x_2311_;
}
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_expr_instantiate_rev(v_e_2298_, v_fvars_2297_);
lean_dec_ref(v_e_2298_);
lean_inc_ref(v_post_2293_);
lean_inc_ref(v_pre_2292_);
v___x_2320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2292_, v_post_2293_, v_usedLetOnly_2294_, v_skipConstInApp_2295_, v_skipInstances_2296_, v___x_2319_, v_a_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; uint8_t v___x_2322_; uint8_t v___x_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = 0;
v___x_2323_ = 1;
v___x_2324_ = 1;
v___x_2325_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2297_, v_a_2321_, v___x_2322_, v_usedLetOnly_2294_, v___x_2322_, v___x_2323_, v___x_2324_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec_ref(v_fvars_2297_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2327_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v___x_2327_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2292_, v_post_2293_, v_usedLetOnly_2294_, v_skipConstInApp_2295_, v_skipInstances_2296_, v_a_2326_, v_a_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
return v___x_2327_;
}
else
{
lean_dec_ref(v_post_2293_);
lean_dec_ref(v_pre_2292_);
return v___x_2325_;
}
}
else
{
lean_dec_ref(v_fvars_2297_);
lean_dec_ref(v_post_2293_);
lean_dec_ref(v_pre_2292_);
return v___x_2320_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_2328_, lean_object* v_pre_2329_, lean_object* v_post_2330_, uint8_t v_usedLetOnly_2331_, uint8_t v_skipConstInApp_2332_, uint8_t v_skipInstances_2333_, lean_object* v_body_2334_, lean_object* v_x_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_array_push(v_fvars_2328_, v_x_2335_);
v___x_2344_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2329_, v_post_2330_, v_usedLetOnly_2331_, v_skipConstInApp_2332_, v_skipInstances_2333_, v___x_2343_, v_body_2334_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_2345_, lean_object* v_pre_2346_, lean_object* v_post_2347_, lean_object* v_usedLetOnly_2348_, lean_object* v_skipConstInApp_2349_, lean_object* v_skipInstances_2350_, lean_object* v_body_2351_, lean_object* v_x_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v_usedLetOnly_boxed_2360_; uint8_t v_skipConstInApp_boxed_2361_; uint8_t v_skipInstances_boxed_2362_; lean_object* v_res_2363_; 
v_usedLetOnly_boxed_2360_ = lean_unbox(v_usedLetOnly_2348_);
v_skipConstInApp_boxed_2361_ = lean_unbox(v_skipConstInApp_2349_);
v_skipInstances_boxed_2362_ = lean_unbox(v_skipInstances_2350_);
v_res_2363_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2345_, v_pre_2346_, v_post_2347_, v_usedLetOnly_boxed_2360_, v_skipConstInApp_boxed_2361_, v_skipInstances_boxed_2362_, v_body_2351_, v_x_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec(v___y_2353_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object* v_pre_2364_, lean_object* v_post_2365_, uint8_t v_usedLetOnly_2366_, uint8_t v_skipConstInApp_2367_, uint8_t v_skipInstances_2368_, lean_object* v_fvars_2369_, lean_object* v_e_2370_, lean_object* v_a_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
if (lean_obj_tag(v_e_2370_) == 8)
{
lean_object* v_declName_2378_; lean_object* v_type_2379_; lean_object* v_value_2380_; lean_object* v_body_2381_; uint8_t v_nondep_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_declName_2378_ = lean_ctor_get(v_e_2370_, 0);
lean_inc(v_declName_2378_);
v_type_2379_ = lean_ctor_get(v_e_2370_, 1);
lean_inc_ref(v_type_2379_);
v_value_2380_ = lean_ctor_get(v_e_2370_, 2);
lean_inc_ref(v_value_2380_);
v_body_2381_ = lean_ctor_get(v_e_2370_, 3);
lean_inc_ref(v_body_2381_);
v_nondep_2382_ = lean_ctor_get_uint8(v_e_2370_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2370_, 4);
v___x_2383_ = lean_expr_instantiate_rev(v_type_2379_, v_fvars_2369_);
lean_dec_ref(v_type_2379_);
lean_inc_ref(v_post_2365_);
lean_inc_ref(v_pre_2364_);
v___x_2384_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2364_, v_post_2365_, v_usedLetOnly_2366_, v_skipConstInApp_2367_, v_skipInstances_2368_, v___x_2383_, v_a_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v___x_2386_ = lean_expr_instantiate_rev(v_value_2380_, v_fvars_2369_);
lean_dec_ref(v_value_2380_);
lean_inc_ref(v_post_2365_);
lean_inc_ref(v_pre_2364_);
v___x_2387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2364_, v_post_2365_, v_usedLetOnly_2366_, v_skipConstInApp_2367_, v_skipInstances_2368_, v___x_2386_, v_a_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___f_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2389_ = lean_box(v_usedLetOnly_2366_);
v___x_2390_ = lean_box(v_skipConstInApp_2367_);
v___x_2391_ = lean_box(v_skipInstances_2368_);
v___f_2392_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2392_, 0, v_fvars_2369_);
lean_closure_set(v___f_2392_, 1, v_pre_2364_);
lean_closure_set(v___f_2392_, 2, v_post_2365_);
lean_closure_set(v___f_2392_, 3, v___x_2389_);
lean_closure_set(v___f_2392_, 4, v___x_2390_);
lean_closure_set(v___f_2392_, 5, v___x_2391_);
lean_closure_set(v___f_2392_, 6, v_body_2381_);
v___x_2393_ = 0;
v___x_2394_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2378_, v_a_2385_, v_a_2388_, v___f_2392_, v_nondep_2382_, v___x_2393_, v_a_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
return v___x_2394_;
}
else
{
lean_dec(v_a_2385_);
lean_dec_ref(v_body_2381_);
lean_dec(v_declName_2378_);
lean_dec_ref(v_fvars_2369_);
lean_dec_ref(v_post_2365_);
lean_dec_ref(v_pre_2364_);
return v___x_2387_;
}
}
else
{
lean_dec_ref(v_body_2381_);
lean_dec_ref(v_value_2380_);
lean_dec(v_declName_2378_);
lean_dec_ref(v_fvars_2369_);
lean_dec_ref(v_post_2365_);
lean_dec_ref(v_pre_2364_);
return v___x_2384_;
}
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_expr_instantiate_rev(v_e_2370_, v_fvars_2369_);
lean_dec_ref(v_e_2370_);
lean_inc_ref(v_post_2365_);
lean_inc_ref(v_pre_2364_);
v___x_2396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2364_, v_post_2365_, v_usedLetOnly_2366_, v_skipConstInApp_2367_, v_skipInstances_2368_, v___x_2395_, v_a_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; uint8_t v___x_2398_; uint8_t v___x_2399_; lean_object* v___x_2400_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v___x_2398_ = 0;
v___x_2399_ = 1;
v___x_2400_ = l_Lean_Meta_mkLetFVars(v_fvars_2369_, v_a_2397_, v_usedLetOnly_2366_, v___x_2398_, v___x_2399_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec_ref(v_fvars_2369_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2402_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2364_, v_post_2365_, v_usedLetOnly_2366_, v_skipConstInApp_2367_, v_skipInstances_2368_, v_a_2401_, v_a_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
return v___x_2402_;
}
else
{
lean_dec_ref(v_post_2365_);
lean_dec_ref(v_pre_2364_);
return v___x_2400_;
}
}
else
{
lean_dec_ref(v_fvars_2369_);
lean_dec_ref(v_post_2365_);
lean_dec_ref(v_pre_2364_);
return v___x_2396_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2403_; lean_object* v_dummy_2404_; 
v___x_2403_ = lean_box(0);
v_dummy_2404_ = l_Lean_Expr_sort___override(v___x_2403_);
return v_dummy_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object* v_pre_2405_, lean_object* v_post_2406_, uint8_t v_usedLetOnly_2407_, uint8_t v_skipConstInApp_2408_, uint8_t v_skipInstances_2409_, size_t v_sz_2410_, size_t v_i_2411_, lean_object* v_bs_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
uint8_t v___x_2420_; 
v___x_2420_ = lean_usize_dec_lt(v_i_2411_, v_sz_2410_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; 
lean_dec_ref(v_post_2406_);
lean_dec_ref(v_pre_2405_);
v___x_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_bs_2412_);
return v___x_2421_;
}
else
{
lean_object* v_v_2422_; lean_object* v___x_2423_; 
v_v_2422_ = lean_array_uget_borrowed(v_bs_2412_, v_i_2411_);
lean_inc(v_v_2422_);
lean_inc_ref(v_post_2406_);
lean_inc_ref(v_pre_2405_);
v___x_2423_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2405_, v_post_2406_, v_usedLetOnly_2407_, v_skipConstInApp_2408_, v_skipInstances_2409_, v_v_2422_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2425_; lean_object* v_bs_x27_2426_; size_t v___x_2427_; size_t v___x_2428_; lean_object* v___x_2429_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
v___x_2425_ = lean_unsigned_to_nat(0u);
v_bs_x27_2426_ = lean_array_uset(v_bs_2412_, v_i_2411_, v___x_2425_);
v___x_2427_ = ((size_t)1ULL);
v___x_2428_ = lean_usize_add(v_i_2411_, v___x_2427_);
v___x_2429_ = lean_array_uset(v_bs_x27_2426_, v_i_2411_, v_a_2424_);
v_i_2411_ = v___x_2428_;
v_bs_2412_ = v___x_2429_;
goto _start;
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec_ref(v_bs_2412_);
lean_dec_ref(v_post_2406_);
lean_dec_ref(v_pre_2405_);
v_a_2431_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2423_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2423_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_2439_, lean_object* v_post_2440_, uint8_t v_usedLetOnly_2441_, uint8_t v_skipConstInApp_2442_, uint8_t v_skipInstances_2443_, lean_object* v___x_2444_, lean_object* v___y_2445_, lean_object* v_b_2446_, lean_object* v_a_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2439_, v_post_2440_, v_usedLetOnly_2441_, v_skipConstInApp_2442_, v_skipInstances_2443_, v___x_2444_, v___y_2445_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2464_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2464_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2464_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2459_ = lean_array_fset(v_b_2446_, v_a_2447_, v_a_2455_);
v___x_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2460_);
v___x_2462_ = v___x_2457_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec_ref(v_b_2446_);
v_a_2465_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2454_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2454_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_2473_, lean_object* v_post_2474_, lean_object* v_usedLetOnly_2475_, lean_object* v_skipConstInApp_2476_, lean_object* v_skipInstances_2477_, lean_object* v___x_2478_, lean_object* v___y_2479_, lean_object* v_b_2480_, lean_object* v_a_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
uint8_t v_usedLetOnly_boxed_2488_; uint8_t v_skipConstInApp_boxed_2489_; uint8_t v_skipInstances_boxed_2490_; lean_object* v_res_2491_; 
v_usedLetOnly_boxed_2488_ = lean_unbox(v_usedLetOnly_2475_);
v_skipConstInApp_boxed_2489_ = lean_unbox(v_skipConstInApp_2476_);
v_skipInstances_boxed_2490_ = lean_unbox(v_skipInstances_2477_);
v_res_2491_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2473_, v_post_2474_, v_usedLetOnly_boxed_2488_, v_skipConstInApp_boxed_2489_, v_skipInstances_boxed_2490_, v___x_2478_, v___y_2479_, v_b_2480_, v_a_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec(v_a_2481_);
lean_dec(v___y_2479_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_2492_, lean_object* v___x_2493_, lean_object* v_pre_2494_, lean_object* v_post_2495_, uint8_t v_usedLetOnly_2496_, uint8_t v_skipConstInApp_2497_, uint8_t v_skipInstances_2498_, lean_object* v_a_2499_, lean_object* v_b_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___y_2509_; uint8_t v___x_2532_; 
v___x_2532_ = lean_nat_dec_lt(v_a_2499_, v_upperBound_2492_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; 
lean_dec(v_a_2499_);
lean_dec_ref(v_post_2495_);
lean_dec_ref(v_pre_2494_);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_b_2500_);
return v___x_2533_;
}
else
{
lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2534_ = lean_array_fget_borrowed(v_b_2500_, v_a_2499_);
v___x_2535_ = lean_array_get_size(v___x_2493_);
v___x_2536_ = lean_nat_dec_lt(v_a_2499_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___f_2540_; 
lean_inc(v___x_2534_);
v___x_2537_ = lean_box(v_usedLetOnly_2496_);
v___x_2538_ = lean_box(v_skipConstInApp_2497_);
v___x_2539_ = lean_box(v_skipInstances_2498_);
lean_inc(v_a_2499_);
lean_inc(v___y_2501_);
lean_inc_ref(v_post_2495_);
lean_inc_ref(v_pre_2494_);
v___f_2540_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2540_, 0, v_pre_2494_);
lean_closure_set(v___f_2540_, 1, v_post_2495_);
lean_closure_set(v___f_2540_, 2, v___x_2537_);
lean_closure_set(v___f_2540_, 3, v___x_2538_);
lean_closure_set(v___f_2540_, 4, v___x_2539_);
lean_closure_set(v___f_2540_, 5, v___x_2534_);
lean_closure_set(v___f_2540_, 6, v___y_2501_);
lean_closure_set(v___f_2540_, 7, v_b_2500_);
lean_closure_set(v___f_2540_, 8, v_a_2499_);
v___y_2509_ = v___f_2540_;
goto v___jp_2508_;
}
else
{
lean_object* v___x_2541_; uint8_t v_isInstance_2542_; 
v___x_2541_ = lean_array_fget_borrowed(v___x_2493_, v_a_2499_);
v_isInstance_2542_ = lean_ctor_get_uint8(v___x_2541_, sizeof(void*)*1 + 4);
if (v_isInstance_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___f_2546_; 
lean_inc(v___x_2534_);
v___x_2543_ = lean_box(v_usedLetOnly_2496_);
v___x_2544_ = lean_box(v_skipConstInApp_2497_);
v___x_2545_ = lean_box(v_skipInstances_2498_);
lean_inc(v_a_2499_);
lean_inc(v___y_2501_);
lean_inc_ref(v_post_2495_);
lean_inc_ref(v_pre_2494_);
v___f_2546_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2546_, 0, v_pre_2494_);
lean_closure_set(v___f_2546_, 1, v_post_2495_);
lean_closure_set(v___f_2546_, 2, v___x_2543_);
lean_closure_set(v___f_2546_, 3, v___x_2544_);
lean_closure_set(v___f_2546_, 4, v___x_2545_);
lean_closure_set(v___f_2546_, 5, v___x_2534_);
lean_closure_set(v___f_2546_, 6, v___y_2501_);
lean_closure_set(v___f_2546_, 7, v_b_2500_);
lean_closure_set(v___f_2546_, 8, v_a_2499_);
v___y_2509_ = v___f_2546_;
goto v___jp_2508_;
}
else
{
lean_object* v___x_2547_; lean_object* v___f_2548_; 
v___x_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_b_2500_);
v___f_2548_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2548_, 0, v___x_2547_);
v___y_2509_ = v___f_2548_;
goto v___jp_2508_;
}
}
}
v___jp_2508_:
{
lean_object* v___x_2510_; 
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
lean_inc(v___y_2502_);
v___x_2510_ = lean_apply_6(v___y_2509_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, lean_box(0));
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2523_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2523_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2523_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
if (lean_obj_tag(v_a_2511_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2517_; 
lean_dec(v_a_2499_);
lean_dec_ref(v_post_2495_);
lean_dec_ref(v_pre_2494_);
v_a_2515_ = lean_ctor_get(v_a_2511_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v_a_2511_, 1);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v_a_2515_);
v___x_2517_ = v___x_2513_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_del_object(v___x_2513_);
v_a_2519_ = lean_ctor_get(v_a_2511_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v_a_2511_, 1);
v___x_2520_ = lean_unsigned_to_nat(1u);
v___x_2521_ = lean_nat_add(v_a_2499_, v___x_2520_);
lean_dec(v_a_2499_);
v_a_2499_ = v___x_2521_;
v_b_2500_ = v_a_2519_;
goto _start;
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v_a_2499_);
lean_dec_ref(v_post_2495_);
lean_dec_ref(v_pre_2494_);
v_a_2524_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2510_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2510_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t v_skipInstances_2549_, lean_object* v_pre_2550_, lean_object* v_post_2551_, uint8_t v_usedLetOnly_2552_, uint8_t v_skipConstInApp_2553_, lean_object* v_x_2554_, lean_object* v_x_2555_, lean_object* v_x_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_f_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; 
if (lean_obj_tag(v_x_2554_) == 5)
{
lean_object* v_fn_2614_; lean_object* v_arg_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_fn_2614_ = lean_ctor_get(v_x_2554_, 0);
lean_inc_ref(v_fn_2614_);
v_arg_2615_ = lean_ctor_get(v_x_2554_, 1);
lean_inc_ref(v_arg_2615_);
lean_dec_ref_known(v_x_2554_, 2);
v___x_2616_ = lean_array_set(v_x_2555_, v_x_2556_, v_arg_2615_);
v___x_2617_ = lean_unsigned_to_nat(1u);
v___x_2618_ = lean_nat_sub(v_x_2556_, v___x_2617_);
lean_dec(v_x_2556_);
v_x_2554_ = v_fn_2614_;
v_x_2555_ = v___x_2616_;
v_x_2556_ = v___x_2618_;
goto _start;
}
else
{
lean_dec(v_x_2556_);
if (v_skipConstInApp_2553_ == 0)
{
goto v___jp_2611_;
}
else
{
uint8_t v___x_2620_; 
v___x_2620_ = l_Lean_Expr_isConst(v_x_2554_);
if (v___x_2620_ == 0)
{
goto v___jp_2611_;
}
else
{
v_f_2565_ = v_x_2554_;
v___y_2566_ = v___y_2557_;
v___y_2567_ = v___y_2558_;
v___y_2568_ = v___y_2559_;
v___y_2569_ = v___y_2560_;
v___y_2570_ = v___y_2561_;
v___y_2571_ = v___y_2562_;
goto v___jp_2564_;
}
}
}
v___jp_2564_:
{
if (v_skipInstances_2549_ == 0)
{
size_t v_sz_2572_; size_t v___x_2573_; lean_object* v___x_2574_; 
v_sz_2572_ = lean_array_size(v_x_2555_);
v___x_2573_ = ((size_t)0ULL);
lean_inc_ref(v_post_2551_);
lean_inc_ref(v_pre_2550_);
v___x_2574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2550_, v_post_2551_, v_usedLetOnly_2552_, v_skipConstInApp_2553_, v_skipInstances_2549_, v_sz_2572_, v___x_2573_, v_x_2555_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2576_ = l_Lean_mkAppN(v_f_2565_, v_a_2575_);
lean_dec(v_a_2575_);
v___x_2577_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2550_, v_post_2551_, v_usedLetOnly_2552_, v_skipConstInApp_2553_, v_skipInstances_2549_, v___x_2576_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2577_;
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec_ref(v_f_2565_);
lean_dec_ref(v_post_2551_);
lean_dec_ref(v_pre_2550_);
v_a_2578_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2574_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2574_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_array_get_size(v_x_2555_);
lean_inc_ref(v_f_2565_);
v___x_2587_ = l_Lean_Meta_getFunInfoNArgs(v_f_2565_, v___x_2586_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v_paramInfo_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2587_, 1);
v_paramInfo_2589_ = lean_ctor_get(v_a_2588_, 0);
lean_inc_ref(v_paramInfo_2589_);
lean_dec(v_a_2588_);
v___x_2590_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2551_);
lean_inc_ref(v_pre_2550_);
v___x_2591_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_2586_, v_paramInfo_2589_, v_pre_2550_, v_post_2551_, v_usedLetOnly_2552_, v_skipConstInApp_2553_, v_skipInstances_2549_, v___x_2590_, v_x_2555_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec_ref(v_paramInfo_2589_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = l_Lean_mkAppN(v_f_2565_, v_a_2592_);
lean_dec(v_a_2592_);
v___x_2594_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2550_, v_post_2551_, v_usedLetOnly_2552_, v_skipConstInApp_2553_, v_skipInstances_2549_, v___x_2593_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2594_;
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v_f_2565_);
lean_dec_ref(v_post_2551_);
lean_dec_ref(v_pre_2550_);
v_a_2595_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2591_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2591_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec_ref(v_f_2565_);
lean_dec_ref(v_x_2555_);
lean_dec_ref(v_post_2551_);
lean_dec_ref(v_pre_2550_);
v_a_2603_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2587_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2587_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
v___jp_2611_:
{
lean_object* v___x_2612_; 
lean_inc_ref(v_post_2551_);
lean_inc_ref(v_pre_2550_);
v___x_2612_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2550_, v_post_2551_, v_usedLetOnly_2552_, v_skipConstInApp_2553_, v_skipInstances_2549_, v_x_2554_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
v_f_2565_ = v_a_2613_;
v___y_2566_ = v___y_2557_;
v___y_2567_ = v___y_2558_;
v___y_2568_ = v___y_2559_;
v___y_2569_ = v___y_2560_;
v___y_2570_ = v___y_2561_;
v___y_2571_ = v___y_2562_;
goto v___jp_2564_;
}
else
{
lean_dec_ref(v_x_2555_);
lean_dec_ref(v_post_2551_);
lean_dec_ref(v_pre_2550_);
return v___x_2612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object* v___x_2621_, lean_object* v_pre_2622_, lean_object* v_e_2623_, lean_object* v_post_2624_, uint8_t v_usedLetOnly_2625_, uint8_t v_skipConstInApp_2626_, uint8_t v_skipInstances_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_Core_checkSystem(v___x_2621_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v___x_2636_; 
lean_dec_ref_known(v___x_2635_, 1);
lean_inc_ref(v_pre_2622_);
lean_inc(v___y_2633_);
lean_inc_ref(v___y_2632_);
lean_inc(v___y_2631_);
lean_inc_ref(v___y_2630_);
lean_inc(v___y_2629_);
lean_inc_ref(v_e_2623_);
v___x_2636_ = lean_apply_7(v_pre_2622_, v_e_2623_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, lean_box(0));
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2685_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2685_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2685_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___y_2642_; 
switch(lean_obj_tag(v_a_2637_))
{
case 0:
{
lean_object* v_e_2677_; lean_object* v___x_2679_; 
lean_dec_ref(v_post_2624_);
lean_dec_ref(v_e_2623_);
lean_dec_ref(v_pre_2622_);
v_e_2677_ = lean_ctor_get(v_a_2637_, 0);
lean_inc_ref(v_e_2677_);
lean_dec_ref_known(v_a_2637_, 1);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_e_2677_);
v___x_2679_ = v___x_2639_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_e_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
case 1:
{
lean_object* v_e_2681_; lean_object* v___x_2682_; 
lean_del_object(v___x_2639_);
lean_dec_ref(v_e_2623_);
v_e_2681_ = lean_ctor_get(v_a_2637_, 0);
lean_inc_ref(v_e_2681_);
lean_dec_ref_known(v_a_2637_, 1);
v___x_2682_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v_skipInstances_2627_, v_e_2681_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2682_;
}
default: 
{
lean_object* v_e_x3f_2683_; 
lean_del_object(v___x_2639_);
v_e_x3f_2683_ = lean_ctor_get(v_a_2637_, 0);
lean_inc(v_e_x3f_2683_);
lean_dec_ref_known(v_a_2637_, 1);
if (lean_obj_tag(v_e_x3f_2683_) == 0)
{
v___y_2642_ = v_e_2623_;
goto v___jp_2641_;
}
else
{
lean_object* v_val_2684_; 
lean_dec_ref(v_e_2623_);
v_val_2684_ = lean_ctor_get(v_e_x3f_2683_, 0);
lean_inc(v_val_2684_);
lean_dec_ref_known(v_e_x3f_2683_, 1);
v___y_2642_ = v_val_2684_;
goto v___jp_2641_;
}
}
}
v___jp_2641_:
{
switch(lean_obj_tag(v___y_2642_))
{
case 7:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2644_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v_skipInstances_2627_, v___x_2643_, v___y_2642_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2644_;
}
case 6:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v_skipInstances_2627_, v___x_2645_, v___y_2642_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2646_;
}
case 8:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2648_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v_skipInstances_2627_, v___x_2647_, v___y_2642_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2648_;
}
case 5:
{
lean_object* v_dummy_2649_; lean_object* v_nargs_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v_dummy_2649_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
v_nargs_2650_ = l_Lean_Expr_getAppNumArgs(v___y_2642_);
lean_inc(v_nargs_2650_);
v___x_2651_ = lean_mk_array(v_nargs_2650_, v_dummy_2649_);
v___x_2652_ = lean_unsigned_to_nat(1u);
v___x_2653_ = lean_nat_sub(v_nargs_2650_, v___x_2652_);
lean_dec(v_nargs_2650_);
v___x_2654_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2627_, v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v___y_2642_, v___x_2651_, v___x_2653_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2654_;
}
case 10:
{
lean_object* v_data_2655_; lean_object* v_expr_2656_; lean_object* v___x_2657_; 
v_data_2655_ = lean_ctor_get(v___y_2642_, 0);
v_expr_2656_ = lean_ctor_get(v___y_2642_, 1);
lean_inc_ref(v_expr_2656_);
lean_inc_ref(v_post_2624_);
lean_inc_ref(v_pre_2622_);
v___x_2657_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v_skipInstances_2627_, v_expr_2656_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; size_t v___x_2659_; size_t v___x_2660_; uint8_t v___x_2661_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = lean_ptr_addr(v_expr_2656_);
v___x_2660_ = lean_ptr_addr(v_a_2658_);
v___x_2661_ = lean_usize_dec_eq(v___x_2659_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_inc(v_data_2655_);
lean_dec_ref_known(v___y_2642_, 2);
v___x_2662_ = l_Lean_Expr_mdata___override(v_data_2655_, v_a_2658_);
v___x_2663_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v_skipInstances_2627_, v___x_2662_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2663_;
}
else
{
lean_object* v___x_2664_; 
lean_dec(v_a_2658_);
v___x_2664_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v_skipInstances_2627_, v___y_2642_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2664_;
}
}
else
{
lean_dec_ref_known(v___y_2642_, 2);
lean_dec_ref(v_post_2624_);
lean_dec_ref(v_pre_2622_);
return v___x_2657_;
}
}
case 11:
{
lean_object* v_typeName_2665_; lean_object* v_idx_2666_; lean_object* v_struct_2667_; lean_object* v___x_2668_; 
v_typeName_2665_ = lean_ctor_get(v___y_2642_, 0);
v_idx_2666_ = lean_ctor_get(v___y_2642_, 1);
v_struct_2667_ = lean_ctor_get(v___y_2642_, 2);
lean_inc_ref(v_struct_2667_);
lean_inc_ref(v_post_2624_);
lean_inc_ref(v_pre_2622_);
v___x_2668_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v_skipInstances_2627_, v_struct_2667_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; size_t v___x_2670_; size_t v___x_2671_; uint8_t v___x_2672_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v___x_2670_ = lean_ptr_addr(v_struct_2667_);
v___x_2671_ = lean_ptr_addr(v_a_2669_);
v___x_2672_ = lean_usize_dec_eq(v___x_2670_, v___x_2671_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_inc(v_idx_2666_);
lean_inc(v_typeName_2665_);
lean_dec_ref_known(v___y_2642_, 3);
v___x_2673_ = l_Lean_Expr_proj___override(v_typeName_2665_, v_idx_2666_, v_a_2669_);
v___x_2674_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v_skipInstances_2627_, v___x_2673_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2674_;
}
else
{
lean_object* v___x_2675_; 
lean_dec(v_a_2669_);
v___x_2675_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v_skipInstances_2627_, v___y_2642_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2675_;
}
}
else
{
lean_dec_ref_known(v___y_2642_, 3);
lean_dec_ref(v_post_2624_);
lean_dec_ref(v_pre_2622_);
return v___x_2668_;
}
}
default: 
{
lean_object* v___x_2676_; 
v___x_2676_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2622_, v_post_2624_, v_usedLetOnly_2625_, v_skipConstInApp_2626_, v_skipInstances_2627_, v___y_2642_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2676_;
}
}
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec_ref(v_post_2624_);
lean_dec_ref(v_e_2623_);
lean_dec_ref(v_pre_2622_);
v_a_2686_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2636_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2636_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v_post_2624_);
lean_dec_ref(v_e_2623_);
lean_dec_ref(v_pre_2622_);
v_a_2694_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2635_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2635_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2702_, lean_object* v_pre_2703_, lean_object* v_e_2704_, lean_object* v_post_2705_, lean_object* v_usedLetOnly_2706_, lean_object* v_skipConstInApp_2707_, lean_object* v_skipInstances_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
uint8_t v_usedLetOnly_boxed_2716_; uint8_t v_skipConstInApp_boxed_2717_; uint8_t v_skipInstances_boxed_2718_; lean_object* v_res_2719_; 
v_usedLetOnly_boxed_2716_ = lean_unbox(v_usedLetOnly_2706_);
v_skipConstInApp_boxed_2717_ = lean_unbox(v_skipConstInApp_2707_);
v_skipInstances_boxed_2718_ = lean_unbox(v_skipInstances_2708_);
v_res_2719_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2702_, v_pre_2703_, v_e_2704_, v_post_2705_, v_usedLetOnly_boxed_2716_, v_skipConstInApp_boxed_2717_, v_skipInstances_boxed_2718_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___y_2709_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object* v_pre_2720_, lean_object* v_post_2721_, uint8_t v_usedLetOnly_2722_, uint8_t v_skipConstInApp_2723_, uint8_t v_skipInstances_2724_, lean_object* v_e_2725_, lean_object* v_a_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
lean_inc(v_a_2726_);
v___x_2733_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2733_, 0, lean_box(0));
lean_closure_set(v___x_2733_, 1, lean_box(0));
lean_closure_set(v___x_2733_, 2, v_a_2726_);
v___x_2734_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_2733_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2769_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2769_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2769_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_2735_, v_e_2725_);
lean_dec(v_a_2735_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___f_2744_; lean_object* v___x_2745_; 
lean_del_object(v___x_2737_);
v___x_2740_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0));
v___x_2741_ = lean_box(v_usedLetOnly_2722_);
v___x_2742_ = lean_box(v_skipConstInApp_2723_);
v___x_2743_ = lean_box(v_skipInstances_2724_);
lean_inc_ref(v_e_2725_);
v___f_2744_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed), 14, 7);
lean_closure_set(v___f_2744_, 0, v___x_2740_);
lean_closure_set(v___f_2744_, 1, v_pre_2720_);
lean_closure_set(v___f_2744_, 2, v_e_2725_);
lean_closure_set(v___f_2744_, 3, v_post_2721_);
lean_closure_set(v___f_2744_, 4, v___x_2741_);
lean_closure_set(v___f_2744_, 5, v___x_2742_);
lean_closure_set(v___f_2744_, 6, v___x_2743_);
v___x_2745_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_2744_, v_a_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___f_2747_; lean_object* v___x_2748_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc_n(v_a_2746_, 2);
lean_dec_ref_known(v___x_2745_, 1);
lean_inc(v_a_2726_);
v___f_2747_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2747_, 0, v_a_2726_);
lean_closure_set(v___f_2747_, 1, v_e_2725_);
lean_closure_set(v___f_2747_, 2, v_a_2746_);
v___x_2748_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_2747_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v___x_2748_, 0);
lean_dec(v_unused_2756_);
v___x_2750_ = v___x_2748_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_dec(v___x_2748_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v_a_2746_);
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2746_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_a_2746_);
v_a_2757_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2748_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2748_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_dec_ref(v_e_2725_);
return v___x_2745_;
}
}
else
{
lean_object* v_val_2765_; lean_object* v___x_2767_; 
lean_dec_ref(v_e_2725_);
lean_dec_ref(v_post_2721_);
lean_dec_ref(v_pre_2720_);
v_val_2765_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_val_2765_);
lean_dec_ref_known(v___x_2739_, 1);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v_val_2765_);
v___x_2767_ = v___x_2737_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_val_2765_);
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
lean_dec_ref(v_e_2725_);
lean_dec_ref(v_post_2721_);
lean_dec_ref(v_pre_2720_);
v_a_2770_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2734_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2734_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2778_, lean_object* v_pre_2779_, lean_object* v_post_2780_, lean_object* v_usedLetOnly_2781_, lean_object* v_skipConstInApp_2782_, lean_object* v_skipInstances_2783_, lean_object* v_body_2784_, lean_object* v_x_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
uint8_t v_usedLetOnly_boxed_2793_; uint8_t v_skipConstInApp_boxed_2794_; uint8_t v_skipInstances_boxed_2795_; lean_object* v_res_2796_; 
v_usedLetOnly_boxed_2793_ = lean_unbox(v_usedLetOnly_2781_);
v_skipConstInApp_boxed_2794_ = lean_unbox(v_skipConstInApp_2782_);
v_skipInstances_boxed_2795_ = lean_unbox(v_skipInstances_2783_);
v_res_2796_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2778_, v_pre_2779_, v_post_2780_, v_usedLetOnly_boxed_2793_, v_skipConstInApp_boxed_2794_, v_skipInstances_boxed_2795_, v_body_2784_, v_x_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec(v___y_2786_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2797_, lean_object* v_post_2798_, uint8_t v_usedLetOnly_2799_, uint8_t v_skipConstInApp_2800_, uint8_t v_skipInstances_2801_, lean_object* v_fvars_2802_, lean_object* v_e_2803_, lean_object* v_a_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
if (lean_obj_tag(v_e_2803_) == 7)
{
lean_object* v_binderName_2811_; lean_object* v_binderType_2812_; lean_object* v_body_2813_; uint8_t v_binderInfo_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_binderName_2811_ = lean_ctor_get(v_e_2803_, 0);
lean_inc(v_binderName_2811_);
v_binderType_2812_ = lean_ctor_get(v_e_2803_, 1);
lean_inc_ref(v_binderType_2812_);
v_body_2813_ = lean_ctor_get(v_e_2803_, 2);
lean_inc_ref(v_body_2813_);
v_binderInfo_2814_ = lean_ctor_get_uint8(v_e_2803_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2803_, 3);
v___x_2815_ = lean_expr_instantiate_rev(v_binderType_2812_, v_fvars_2802_);
lean_dec_ref(v_binderType_2812_);
lean_inc_ref(v_post_2798_);
lean_inc_ref(v_pre_2797_);
v___x_2816_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2797_, v_post_2798_, v_usedLetOnly_2799_, v_skipConstInApp_2800_, v_skipInstances_2801_, v___x_2815_, v_a_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___f_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
v___x_2818_ = lean_box(v_usedLetOnly_2799_);
v___x_2819_ = lean_box(v_skipConstInApp_2800_);
v___x_2820_ = lean_box(v_skipInstances_2801_);
v___f_2821_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2821_, 0, v_fvars_2802_);
lean_closure_set(v___f_2821_, 1, v_pre_2797_);
lean_closure_set(v___f_2821_, 2, v_post_2798_);
lean_closure_set(v___f_2821_, 3, v___x_2818_);
lean_closure_set(v___f_2821_, 4, v___x_2819_);
lean_closure_set(v___f_2821_, 5, v___x_2820_);
lean_closure_set(v___f_2821_, 6, v_body_2813_);
v___x_2822_ = 0;
v___x_2823_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2811_, v_binderInfo_2814_, v_a_2817_, v___f_2821_, v___x_2822_, v_a_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
return v___x_2823_;
}
else
{
lean_dec_ref(v_body_2813_);
lean_dec(v_binderName_2811_);
lean_dec_ref(v_fvars_2802_);
lean_dec_ref(v_post_2798_);
lean_dec_ref(v_pre_2797_);
return v___x_2816_;
}
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_expr_instantiate_rev(v_e_2803_, v_fvars_2802_);
lean_dec_ref(v_e_2803_);
lean_inc_ref(v_post_2798_);
lean_inc_ref(v_pre_2797_);
v___x_2825_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2797_, v_post_2798_, v_usedLetOnly_2799_, v_skipConstInApp_2800_, v_skipInstances_2801_, v___x_2824_, v_a_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; uint8_t v___x_2827_; uint8_t v___x_2828_; uint8_t v___x_2829_; lean_object* v___x_2830_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = 0;
v___x_2828_ = 1;
v___x_2829_ = 1;
v___x_2830_ = l_Lean_Meta_mkForallFVars(v_fvars_2802_, v_a_2826_, v___x_2827_, v_usedLetOnly_2799_, v___x_2828_, v___x_2829_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec_ref(v_fvars_2802_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v___x_2832_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2797_, v_post_2798_, v_usedLetOnly_2799_, v_skipConstInApp_2800_, v_skipInstances_2801_, v_a_2831_, v_a_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
return v___x_2832_;
}
else
{
lean_dec_ref(v_post_2798_);
lean_dec_ref(v_pre_2797_);
return v___x_2830_;
}
}
else
{
lean_dec_ref(v_fvars_2802_);
lean_dec_ref(v_post_2798_);
lean_dec_ref(v_pre_2797_);
return v___x_2825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2833_, lean_object* v_pre_2834_, lean_object* v_post_2835_, uint8_t v_usedLetOnly_2836_, uint8_t v_skipConstInApp_2837_, uint8_t v_skipInstances_2838_, lean_object* v_body_2839_, lean_object* v_x_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_array_push(v_fvars_2833_, v_x_2840_);
v___x_2849_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2834_, v_post_2835_, v_usedLetOnly_2836_, v_skipConstInApp_2837_, v_skipInstances_2838_, v___x_2848_, v_body_2839_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2850_, lean_object* v_post_2851_, lean_object* v_usedLetOnly_2852_, lean_object* v_skipConstInApp_2853_, lean_object* v_skipInstances_2854_, lean_object* v_e_2855_, lean_object* v_a_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
uint8_t v_usedLetOnly_boxed_2863_; uint8_t v_skipConstInApp_boxed_2864_; uint8_t v_skipInstances_boxed_2865_; lean_object* v_res_2866_; 
v_usedLetOnly_boxed_2863_ = lean_unbox(v_usedLetOnly_2852_);
v_skipConstInApp_boxed_2864_ = lean_unbox(v_skipConstInApp_2853_);
v_skipInstances_boxed_2865_ = lean_unbox(v_skipInstances_2854_);
v_res_2866_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2850_, v_post_2851_, v_usedLetOnly_boxed_2863_, v_skipConstInApp_boxed_2864_, v_skipInstances_boxed_2865_, v_e_2855_, v_a_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec(v_a_2856_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2867_, lean_object* v_post_2868_, lean_object* v_usedLetOnly_2869_, lean_object* v_skipConstInApp_2870_, lean_object* v_skipInstances_2871_, lean_object* v_sz_2872_, lean_object* v_i_2873_, lean_object* v_bs_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
uint8_t v_usedLetOnly_boxed_2882_; uint8_t v_skipConstInApp_boxed_2883_; uint8_t v_skipInstances_boxed_2884_; size_t v_sz_boxed_2885_; size_t v_i_boxed_2886_; lean_object* v_res_2887_; 
v_usedLetOnly_boxed_2882_ = lean_unbox(v_usedLetOnly_2869_);
v_skipConstInApp_boxed_2883_ = lean_unbox(v_skipConstInApp_2870_);
v_skipInstances_boxed_2884_ = lean_unbox(v_skipInstances_2871_);
v_sz_boxed_2885_ = lean_unbox_usize(v_sz_2872_);
lean_dec(v_sz_2872_);
v_i_boxed_2886_ = lean_unbox_usize(v_i_2873_);
lean_dec(v_i_2873_);
v_res_2887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2867_, v_post_2868_, v_usedLetOnly_boxed_2882_, v_skipConstInApp_boxed_2883_, v_skipInstances_boxed_2884_, v_sz_boxed_2885_, v_i_boxed_2886_, v_bs_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2875_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_2888_, lean_object* v_post_2889_, lean_object* v_usedLetOnly_2890_, lean_object* v_skipConstInApp_2891_, lean_object* v_skipInstances_2892_, lean_object* v_e_2893_, lean_object* v_a_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
uint8_t v_usedLetOnly_boxed_2901_; uint8_t v_skipConstInApp_boxed_2902_; uint8_t v_skipInstances_boxed_2903_; lean_object* v_res_2904_; 
v_usedLetOnly_boxed_2901_ = lean_unbox(v_usedLetOnly_2890_);
v_skipConstInApp_boxed_2902_ = lean_unbox(v_skipConstInApp_2891_);
v_skipInstances_boxed_2903_ = lean_unbox(v_skipInstances_2892_);
v_res_2904_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2888_, v_post_2889_, v_usedLetOnly_boxed_2901_, v_skipConstInApp_boxed_2902_, v_skipInstances_boxed_2903_, v_e_2893_, v_a_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec(v_a_2894_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_2905_, lean_object* v_post_2906_, lean_object* v_usedLetOnly_2907_, lean_object* v_skipConstInApp_2908_, lean_object* v_skipInstances_2909_, lean_object* v_fvars_2910_, lean_object* v_e_2911_, lean_object* v_a_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
uint8_t v_usedLetOnly_boxed_2919_; uint8_t v_skipConstInApp_boxed_2920_; uint8_t v_skipInstances_boxed_2921_; lean_object* v_res_2922_; 
v_usedLetOnly_boxed_2919_ = lean_unbox(v_usedLetOnly_2907_);
v_skipConstInApp_boxed_2920_ = lean_unbox(v_skipConstInApp_2908_);
v_skipInstances_boxed_2921_ = lean_unbox(v_skipInstances_2909_);
v_res_2922_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2905_, v_post_2906_, v_usedLetOnly_boxed_2919_, v_skipConstInApp_boxed_2920_, v_skipInstances_boxed_2921_, v_fvars_2910_, v_e_2911_, v_a_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec(v_a_2912_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_2923_, lean_object* v_post_2924_, lean_object* v_usedLetOnly_2925_, lean_object* v_skipConstInApp_2926_, lean_object* v_skipInstances_2927_, lean_object* v_fvars_2928_, lean_object* v_e_2929_, lean_object* v_a_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
uint8_t v_usedLetOnly_boxed_2937_; uint8_t v_skipConstInApp_boxed_2938_; uint8_t v_skipInstances_boxed_2939_; lean_object* v_res_2940_; 
v_usedLetOnly_boxed_2937_ = lean_unbox(v_usedLetOnly_2925_);
v_skipConstInApp_boxed_2938_ = lean_unbox(v_skipConstInApp_2926_);
v_skipInstances_boxed_2939_ = lean_unbox(v_skipInstances_2927_);
v_res_2940_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2923_, v_post_2924_, v_usedLetOnly_boxed_2937_, v_skipConstInApp_boxed_2938_, v_skipInstances_boxed_2939_, v_fvars_2928_, v_e_2929_, v_a_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec(v_a_2930_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_2941_, lean_object* v_post_2942_, lean_object* v_usedLetOnly_2943_, lean_object* v_skipConstInApp_2944_, lean_object* v_skipInstances_2945_, lean_object* v_fvars_2946_, lean_object* v_e_2947_, lean_object* v_a_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
uint8_t v_usedLetOnly_boxed_2955_; uint8_t v_skipConstInApp_boxed_2956_; uint8_t v_skipInstances_boxed_2957_; lean_object* v_res_2958_; 
v_usedLetOnly_boxed_2955_ = lean_unbox(v_usedLetOnly_2943_);
v_skipConstInApp_boxed_2956_ = lean_unbox(v_skipConstInApp_2944_);
v_skipInstances_boxed_2957_ = lean_unbox(v_skipInstances_2945_);
v_res_2958_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2941_, v_post_2942_, v_usedLetOnly_boxed_2955_, v_skipConstInApp_boxed_2956_, v_skipInstances_boxed_2957_, v_fvars_2946_, v_e_2947_, v_a_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec(v_a_2948_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_2959_, lean_object* v___x_2960_, lean_object* v_pre_2961_, lean_object* v_post_2962_, lean_object* v_usedLetOnly_2963_, lean_object* v_skipConstInApp_2964_, lean_object* v_skipInstances_2965_, lean_object* v_a_2966_, lean_object* v_b_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
uint8_t v_usedLetOnly_boxed_2975_; uint8_t v_skipConstInApp_boxed_2976_; uint8_t v_skipInstances_boxed_2977_; lean_object* v_res_2978_; 
v_usedLetOnly_boxed_2975_ = lean_unbox(v_usedLetOnly_2963_);
v_skipConstInApp_boxed_2976_ = lean_unbox(v_skipConstInApp_2964_);
v_skipInstances_boxed_2977_ = lean_unbox(v_skipInstances_2965_);
v_res_2978_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_2959_, v___x_2960_, v_pre_2961_, v_post_2962_, v_usedLetOnly_boxed_2975_, v_skipConstInApp_boxed_2976_, v_skipInstances_boxed_2977_, v_a_2966_, v_b_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___x_2960_);
lean_dec(v_upperBound_2959_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_2979_, lean_object* v_pre_2980_, lean_object* v_post_2981_, lean_object* v_usedLetOnly_2982_, lean_object* v_skipConstInApp_2983_, lean_object* v_x_2984_, lean_object* v_x_2985_, lean_object* v_x_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
uint8_t v_skipInstances_boxed_2994_; uint8_t v_usedLetOnly_boxed_2995_; uint8_t v_skipConstInApp_boxed_2996_; lean_object* v_res_2997_; 
v_skipInstances_boxed_2994_ = lean_unbox(v_skipInstances_2979_);
v_usedLetOnly_boxed_2995_ = lean_unbox(v_usedLetOnly_2982_);
v_skipConstInApp_boxed_2996_ = lean_unbox(v_skipConstInApp_2983_);
v_res_2997_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_2994_, v_pre_2980_, v_post_2981_, v_usedLetOnly_boxed_2995_, v_skipConstInApp_boxed_2996_, v_x_2984_, v_x_2985_, v_x_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_2998_, lean_object* v_x_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = lean_apply_1(v_x_2999_, lean_box(0));
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3008_, lean_object* v_x_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_3008_, v_x_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
return v_res_3016_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = lean_box(0);
v___x_3018_ = lean_unsigned_to_nat(16u);
v___x_3019_ = lean_mk_array(v___x_3018_, v___x_3017_);
return v___x_3019_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
v___x_3021_ = lean_unsigned_to_nat(0u);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v___x_3020_);
return v___x_3022_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3024_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3024_, 0, lean_box(0));
lean_closure_set(v___x_3024_, 1, lean_box(0));
lean_closure_set(v___x_3024_, 2, v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3025_, lean_object* v_pre_3026_, lean_object* v_post_3027_, uint8_t v_usedLetOnly_3028_, uint8_t v_skipConstInApp_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v_a_3038_; uint8_t v___x_3039_; lean_object* v___x_3040_; 
v___x_3036_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3037_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3036_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref(v___x_3037_);
v___x_3039_ = 0;
v___x_3040_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3026_, v_post_3027_, v_usedLetOnly_3028_, v_skipConstInApp_3029_, v___x_3039_, v_input_3025_, v_a_3038_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
v___x_3042_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3042_, 0, lean_box(0));
lean_closure_set(v___x_3042_, 1, lean_box(0));
lean_closure_set(v___x_3042_, 2, v_a_3038_);
v___x_3043_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3042_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3050_ == 0)
{
lean_object* v_unused_3051_; 
v_unused_3051_ = lean_ctor_get(v___x_3043_, 0);
lean_dec(v_unused_3051_);
v___x_3045_ = v___x_3043_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v___x_3043_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v_a_3041_);
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3041_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
else
{
lean_dec(v_a_3038_);
return v___x_3040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3052_, lean_object* v_pre_3053_, lean_object* v_post_3054_, lean_object* v_usedLetOnly_3055_, lean_object* v_skipConstInApp_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
uint8_t v_usedLetOnly_boxed_3063_; uint8_t v_skipConstInApp_boxed_3064_; lean_object* v_res_3065_; 
v_usedLetOnly_boxed_3063_ = lean_unbox(v_usedLetOnly_3055_);
v_skipConstInApp_boxed_3064_ = lean_unbox(v_skipConstInApp_3056_);
v_res_3065_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3052_, v_pre_3053_, v_post_3054_, v_usedLetOnly_boxed_3063_, v_skipConstInApp_boxed_3064_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3067_, uint8_t v_elimTrivial_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v_pre_3077_; lean_object* v___f_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; 
v___x_3074_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_3075_ = lean_st_mk_ref(v___x_3074_);
v___x_3076_ = lean_box(v_elimTrivial_3068_);
v_pre_3077_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3077_, 0, v___x_3076_);
v___f_3078_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0));
v___x_3079_ = 0;
v___x_3080_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3067_, v_pre_3077_, v___f_3078_, v___x_3079_, v___x_3079_, v___x_3075_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3089_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3089_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3089_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3085_ = lean_st_ref_get(v___x_3075_);
lean_dec(v___x_3075_);
lean_dec(v___x_3085_);
if (v_isShared_3084_ == 0)
{
v___x_3087_ = v___x_3083_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3081_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
else
{
lean_dec(v___x_3075_);
return v___x_3080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3090_, lean_object* v_elimTrivial_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
uint8_t v_elimTrivial_boxed_3097_; lean_object* v_res_3098_; 
v_elimTrivial_boxed_3097_ = lean_unbox(v_elimTrivial_3091_);
v_res_3098_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3090_, v_elimTrivial_boxed_3097_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_upperBound_3099_, lean_object* v___x_3100_, lean_object* v_pre_3101_, lean_object* v_post_3102_, uint8_t v_usedLetOnly_3103_, uint8_t v_skipConstInApp_3104_, uint8_t v_skipInstances_3105_, lean_object* v___x_3106_, lean_object* v_inst_3107_, lean_object* v_R_3108_, lean_object* v_a_3109_, lean_object* v_b_3110_, lean_object* v_c_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3099_, v___x_3100_, v_pre_3101_, v_post_3102_, v_usedLetOnly_3103_, v_skipConstInApp_3104_, v_skipInstances_3105_, v_a_3109_, v_b_3110_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3120_ = _args[0];
lean_object* v___x_3121_ = _args[1];
lean_object* v_pre_3122_ = _args[2];
lean_object* v_post_3123_ = _args[3];
lean_object* v_usedLetOnly_3124_ = _args[4];
lean_object* v_skipConstInApp_3125_ = _args[5];
lean_object* v_skipInstances_3126_ = _args[6];
lean_object* v___x_3127_ = _args[7];
lean_object* v_inst_3128_ = _args[8];
lean_object* v_R_3129_ = _args[9];
lean_object* v_a_3130_ = _args[10];
lean_object* v_b_3131_ = _args[11];
lean_object* v_c_3132_ = _args[12];
lean_object* v___y_3133_ = _args[13];
lean_object* v___y_3134_ = _args[14];
lean_object* v___y_3135_ = _args[15];
lean_object* v___y_3136_ = _args[16];
lean_object* v___y_3137_ = _args[17];
lean_object* v___y_3138_ = _args[18];
lean_object* v___y_3139_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3140_; uint8_t v_skipConstInApp_boxed_3141_; uint8_t v_skipInstances_boxed_3142_; lean_object* v_res_3143_; 
v_usedLetOnly_boxed_3140_ = lean_unbox(v_usedLetOnly_3124_);
v_skipConstInApp_boxed_3141_ = lean_unbox(v_skipConstInApp_3125_);
v_skipInstances_boxed_3142_ = lean_unbox(v_skipInstances_3126_);
v_res_3143_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3120_, v___x_3121_, v_pre_3122_, v_post_3123_, v_usedLetOnly_boxed_3140_, v_skipConstInApp_boxed_3141_, v_skipInstances_boxed_3142_, v___x_3127_, v_inst_3128_, v_R_3129_, v_a_3130_, v_b_3131_, v_c_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec(v___x_3127_);
lean_dec_ref(v___x_3121_);
lean_dec(v_upperBound_3120_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3144_, lean_object* v_m_3145_, lean_object* v_a_3146_){
_start:
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_3145_, v_a_3146_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_3148_, lean_object* v_m_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_3148_, v_m_3149_, v_a_3150_);
lean_dec_ref(v_a_3150_);
lean_dec_ref(v_m_3149_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3152_, lean_object* v_name_3153_, uint8_t v_bi_3154_, lean_object* v_type_3155_, lean_object* v_k_3156_, uint8_t v_kind_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3153_, v_bi_3154_, v_type_3155_, v_k_3156_, v_kind_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3166_, lean_object* v_name_3167_, lean_object* v_bi_3168_, lean_object* v_type_3169_, lean_object* v_k_3170_, lean_object* v_kind_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
uint8_t v_bi_boxed_3179_; uint8_t v_kind_boxed_3180_; lean_object* v_res_3181_; 
v_bi_boxed_3179_ = lean_unbox(v_bi_3168_);
v_kind_boxed_3180_ = lean_unbox(v_kind_3171_);
v_res_3181_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3166_, v_name_3167_, v_bi_boxed_3179_, v_type_3169_, v_k_3170_, v_kind_boxed_3180_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec(v___y_3172_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3182_, lean_object* v_name_3183_, lean_object* v_type_3184_, lean_object* v_val_3185_, lean_object* v_k_3186_, uint8_t v_nondep_3187_, uint8_t v_kind_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3183_, v_type_3184_, v_val_3185_, v_k_3186_, v_nondep_3187_, v_kind_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3197_, lean_object* v_name_3198_, lean_object* v_type_3199_, lean_object* v_val_3200_, lean_object* v_k_3201_, lean_object* v_nondep_3202_, lean_object* v_kind_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
uint8_t v_nondep_boxed_3211_; uint8_t v_kind_boxed_3212_; lean_object* v_res_3213_; 
v_nondep_boxed_3211_ = lean_unbox(v_nondep_3202_);
v_kind_boxed_3212_ = lean_unbox(v_kind_3203_);
v_res_3213_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3197_, v_name_3198_, v_type_3199_, v_val_3200_, v_k_3201_, v_nondep_boxed_3211_, v_kind_boxed_3212_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec(v___y_3204_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3214_, lean_object* v_ref_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3215_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3222_, lean_object* v_ref_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3222_, v_ref_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3230_, lean_object* v_x_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3240_, lean_object* v_x_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3240_, v_x_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec(v___y_3242_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3250_, lean_object* v_m_3251_, lean_object* v_a_3252_, lean_object* v_b_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3251_, v_a_3252_, v_b_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_3255_, lean_object* v_a_3256_, lean_object* v_x_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_3256_, v_x_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3259_, lean_object* v_a_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_3259_, v_a_3260_, v_x_3261_);
lean_dec(v_x_3261_);
lean_dec_ref(v_a_3260_);
return v_res_3262_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3263_, lean_object* v_a_3264_, lean_object* v_x_3265_){
_start:
{
uint8_t v___x_3266_; 
v___x_3266_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_3264_, v_x_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3267_, lean_object* v_a_3268_, lean_object* v_x_3269_){
_start:
{
uint8_t v_res_3270_; lean_object* v_r_3271_; 
v_res_3270_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3267_, v_a_3268_, v_x_3269_);
lean_dec(v_x_3269_);
lean_dec_ref(v_a_3268_);
v_r_3271_ = lean_box(v_res_3270_);
return v_r_3271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_3272_, lean_object* v_data_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_3275_, lean_object* v_a_3276_, lean_object* v_b_3277_, lean_object* v_x_3278_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_3276_, v_b_3277_, v_x_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_3280_, lean_object* v_i_3281_, lean_object* v_source_3282_, lean_object* v_target_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_3281_, v_source_3282_, v_target_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3286_, v_x_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3289_, lean_object* v_x_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3289_, v_x_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
v_a_3305_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3296_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3296_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3313_, lean_object* v_x_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3313_, v_x_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3321_, lean_object* v_mvarId_3322_, lean_object* v_x_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3322_, v_x_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3330_, lean_object* v_mvarId_3331_, lean_object* v_x_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3330_, v_mvarId_3331_, v_x_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3339_, lean_object* v_as_3340_, size_t v_sz_3341_, size_t v_i_3342_, lean_object* v_b_3343_){
_start:
{
uint8_t v___x_3345_; 
v___x_3345_ = lean_usize_dec_lt(v_i_3342_, v_sz_3341_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3346_, 0, v_b_3343_);
return v___x_3346_;
}
else
{
lean_object* v_snd_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3394_; 
v_snd_3347_ = lean_ctor_get(v_b_3343_, 1);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_b_3343_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; 
v_unused_3395_ = lean_ctor_get(v_b_3343_, 0);
lean_dec(v_unused_3395_);
v___x_3349_ = v_b_3343_;
v_isShared_3350_ = v_isSharedCheck_3394_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_snd_3347_);
lean_dec(v_b_3343_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3394_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v_a_3353_; lean_object* v_a_3360_; 
v___x_3351_ = lean_box(0);
v_a_3360_ = lean_array_uget_borrowed(v_as_3340_, v_i_3342_);
if (lean_obj_tag(v_a_3360_) == 0)
{
v_a_3353_ = v_snd_3347_;
goto v___jp_3352_;
}
else
{
lean_object* v_val_3361_; lean_object* v_fst_3362_; lean_object* v_snd_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3393_; 
v_val_3361_ = lean_ctor_get(v_a_3360_, 0);
v_fst_3362_ = lean_ctor_get(v_snd_3347_, 0);
v_snd_3363_ = lean_ctor_get(v_snd_3347_, 1);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_snd_3347_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3365_ = v_snd_3347_;
v_isShared_3366_ = v_isSharedCheck_3393_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_snd_3363_);
lean_inc(v_fst_3362_);
lean_dec(v_snd_3347_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3393_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
uint8_t v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = 0;
v___x_3368_ = l_Lean_LocalDecl_value_x3f(v_val_3361_, v___x_3367_);
if (lean_obj_tag(v___x_3368_) == 1)
{
lean_object* v_val_3369_; lean_object* v___x_3370_; 
v_val_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v___x_3368_, 1);
v___x_3370_ = l_Lean_LocalDecl_type(v_val_3361_);
if (lean_obj_tag(v___x_3370_) == 10)
{
lean_object* v_data_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; uint8_t v___x_3376_; 
v_data_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_data_3371_);
lean_dec_ref_known(v___x_3370_, 2);
v___x_3372_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3373_ = lean_unsigned_to_nat(2u);
v___x_3374_ = l_Lean_KVMap_getNat(v_data_3371_, v___x_3372_, v___x_3373_);
lean_dec(v_data_3371_);
v___x_3375_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3374_);
lean_dec(v___x_3374_);
v___x_3376_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3375_, v_val_3369_, v_elimTrivial_3339_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3382_; 
v___x_3377_ = l_Lean_LocalDecl_fvarId(v_val_3361_);
v___x_3378_ = l_Lean_mkFVar(v___x_3377_);
v___x_3379_ = lean_array_push(v_fst_3362_, v___x_3378_);
v___x_3380_ = lean_array_push(v_snd_3363_, v_val_3369_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 1, v___x_3380_);
lean_ctor_set(v___x_3365_, 0, v___x_3379_);
v___x_3382_ = v___x_3365_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
v_a_3353_ = v___x_3382_;
goto v___jp_3352_;
}
}
else
{
lean_object* v___x_3385_; 
lean_dec(v_val_3369_);
if (v_isShared_3366_ == 0)
{
v___x_3385_ = v___x_3365_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_fst_3362_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_snd_3363_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
v_a_3353_ = v___x_3385_;
goto v___jp_3352_;
}
}
}
else
{
lean_object* v___x_3388_; 
lean_dec_ref(v___x_3370_);
lean_dec(v_val_3369_);
if (v_isShared_3366_ == 0)
{
v___x_3388_ = v___x_3365_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_fst_3362_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_snd_3363_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
v_a_3353_ = v___x_3388_;
goto v___jp_3352_;
}
}
}
else
{
lean_object* v___x_3391_; 
lean_dec(v___x_3368_);
if (v_isShared_3366_ == 0)
{
v___x_3391_ = v___x_3365_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_fst_3362_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_snd_3363_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
v_a_3353_ = v___x_3391_;
goto v___jp_3352_;
}
}
}
}
v___jp_3352_:
{
lean_object* v___x_3355_; 
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 1, v_a_3353_);
lean_ctor_set(v___x_3349_, 0, v___x_3351_);
v___x_3355_ = v___x_3349_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3351_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v_a_3353_);
v___x_3355_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
size_t v___x_3356_; size_t v___x_3357_; 
v___x_3356_ = ((size_t)1ULL);
v___x_3357_ = lean_usize_add(v_i_3342_, v___x_3356_);
v_i_3342_ = v___x_3357_;
v_b_3343_ = v___x_3355_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3396_, lean_object* v_as_3397_, lean_object* v_sz_3398_, lean_object* v_i_3399_, lean_object* v_b_3400_, lean_object* v___y_3401_){
_start:
{
uint8_t v_elimTrivial_boxed_3402_; size_t v_sz_boxed_3403_; size_t v_i_boxed_3404_; lean_object* v_res_3405_; 
v_elimTrivial_boxed_3402_ = lean_unbox(v_elimTrivial_3396_);
v_sz_boxed_3403_ = lean_unbox_usize(v_sz_3398_);
lean_dec(v_sz_3398_);
v_i_boxed_3404_ = lean_unbox_usize(v_i_3399_);
lean_dec(v_i_3399_);
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3402_, v_as_3397_, v_sz_boxed_3403_, v_i_boxed_3404_, v_b_3400_);
lean_dec_ref(v_as_3397_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3406_, lean_object* v_as_3407_, size_t v_sz_3408_, size_t v_i_3409_, lean_object* v_b_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
uint8_t v___x_3416_; 
v___x_3416_ = lean_usize_dec_lt(v_i_3409_, v_sz_3408_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3417_, 0, v_b_3410_);
return v___x_3417_;
}
else
{
lean_object* v_snd_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3465_; 
v_snd_3418_ = lean_ctor_get(v_b_3410_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_b_3410_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v_b_3410_, 0);
lean_dec(v_unused_3466_);
v___x_3420_ = v_b_3410_;
v_isShared_3421_ = v_isSharedCheck_3465_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_snd_3418_);
lean_dec(v_b_3410_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3465_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v_a_3424_; lean_object* v_a_3431_; 
v___x_3422_ = lean_box(0);
v_a_3431_ = lean_array_uget_borrowed(v_as_3407_, v_i_3409_);
if (lean_obj_tag(v_a_3431_) == 0)
{
v_a_3424_ = v_snd_3418_;
goto v___jp_3423_;
}
else
{
lean_object* v_val_3432_; lean_object* v_fst_3433_; lean_object* v_snd_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3464_; 
v_val_3432_ = lean_ctor_get(v_a_3431_, 0);
v_fst_3433_ = lean_ctor_get(v_snd_3418_, 0);
v_snd_3434_ = lean_ctor_get(v_snd_3418_, 1);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_snd_3418_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3436_ = v_snd_3418_;
v_isShared_3437_ = v_isSharedCheck_3464_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_snd_3434_);
lean_inc(v_fst_3433_);
lean_dec(v_snd_3418_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3464_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
uint8_t v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = 0;
v___x_3439_ = l_Lean_LocalDecl_value_x3f(v_val_3432_, v___x_3438_);
if (lean_obj_tag(v___x_3439_) == 1)
{
lean_object* v_val_3440_; lean_object* v___x_3441_; 
v_val_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_val_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v___x_3441_ = l_Lean_LocalDecl_type(v_val_3432_);
if (lean_obj_tag(v___x_3441_) == 10)
{
lean_object* v_data_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; uint8_t v___x_3447_; 
v_data_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_data_3442_);
lean_dec_ref_known(v___x_3441_, 2);
v___x_3443_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3444_ = lean_unsigned_to_nat(2u);
v___x_3445_ = l_Lean_KVMap_getNat(v_data_3442_, v___x_3443_, v___x_3444_);
lean_dec(v_data_3442_);
v___x_3446_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3445_);
lean_dec(v___x_3445_);
v___x_3447_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3446_, v_val_3440_, v_elimTrivial_3406_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3448_ = l_Lean_LocalDecl_fvarId(v_val_3432_);
v___x_3449_ = l_Lean_mkFVar(v___x_3448_);
v___x_3450_ = lean_array_push(v_fst_3433_, v___x_3449_);
v___x_3451_ = lean_array_push(v_snd_3434_, v_val_3440_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v___x_3451_);
lean_ctor_set(v___x_3436_, 0, v___x_3450_);
v___x_3453_ = v___x_3436_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
v_a_3424_ = v___x_3453_;
goto v___jp_3423_;
}
}
else
{
lean_object* v___x_3456_; 
lean_dec(v_val_3440_);
if (v_isShared_3437_ == 0)
{
v___x_3456_ = v___x_3436_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_fst_3433_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_snd_3434_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
v_a_3424_ = v___x_3456_;
goto v___jp_3423_;
}
}
}
else
{
lean_object* v___x_3459_; 
lean_dec_ref(v___x_3441_);
lean_dec(v_val_3440_);
if (v_isShared_3437_ == 0)
{
v___x_3459_ = v___x_3436_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_fst_3433_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_snd_3434_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
v_a_3424_ = v___x_3459_;
goto v___jp_3423_;
}
}
}
else
{
lean_object* v___x_3462_; 
lean_dec(v___x_3439_);
if (v_isShared_3437_ == 0)
{
v___x_3462_ = v___x_3436_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_fst_3433_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_snd_3434_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
v_a_3424_ = v___x_3462_;
goto v___jp_3423_;
}
}
}
}
v___jp_3423_:
{
lean_object* v___x_3426_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 1, v_a_3424_);
lean_ctor_set(v___x_3420_, 0, v___x_3422_);
v___x_3426_ = v___x_3420_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_a_3424_);
v___x_3426_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
size_t v___x_3427_; size_t v___x_3428_; lean_object* v___x_3429_; 
v___x_3427_ = ((size_t)1ULL);
v___x_3428_ = lean_usize_add(v_i_3409_, v___x_3427_);
v___x_3429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3406_, v_as_3407_, v_sz_3408_, v___x_3428_, v___x_3426_);
return v___x_3429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3467_, lean_object* v_as_3468_, lean_object* v_sz_3469_, lean_object* v_i_3470_, lean_object* v_b_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
uint8_t v_elimTrivial_boxed_3477_; size_t v_sz_boxed_3478_; size_t v_i_boxed_3479_; lean_object* v_res_3480_; 
v_elimTrivial_boxed_3477_ = lean_unbox(v_elimTrivial_3467_);
v_sz_boxed_3478_ = lean_unbox_usize(v_sz_3469_);
lean_dec(v_sz_3469_);
v_i_boxed_3479_ = lean_unbox_usize(v_i_3470_);
lean_dec(v_i_3470_);
v_res_3480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3477_, v_as_3468_, v_sz_boxed_3478_, v_i_boxed_3479_, v_b_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec_ref(v_as_3468_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3481_, lean_object* v_as_3482_, size_t v_sz_3483_, size_t v_i_3484_, lean_object* v_b_3485_){
_start:
{
uint8_t v___x_3487_; 
v___x_3487_ = lean_usize_dec_lt(v_i_3484_, v_sz_3483_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_b_3485_);
return v___x_3488_;
}
else
{
lean_object* v_snd_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3536_; 
v_snd_3489_ = lean_ctor_get(v_b_3485_, 1);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_b_3485_);
if (v_isSharedCheck_3536_ == 0)
{
lean_object* v_unused_3537_; 
v_unused_3537_ = lean_ctor_get(v_b_3485_, 0);
lean_dec(v_unused_3537_);
v___x_3491_ = v_b_3485_;
v_isShared_3492_ = v_isSharedCheck_3536_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_snd_3489_);
lean_dec(v_b_3485_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3536_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v_a_3495_; lean_object* v_a_3502_; 
v___x_3493_ = lean_box(0);
v_a_3502_ = lean_array_uget_borrowed(v_as_3482_, v_i_3484_);
if (lean_obj_tag(v_a_3502_) == 0)
{
v_a_3495_ = v_snd_3489_;
goto v___jp_3494_;
}
else
{
lean_object* v_val_3503_; lean_object* v_fst_3504_; lean_object* v_snd_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3535_; 
v_val_3503_ = lean_ctor_get(v_a_3502_, 0);
v_fst_3504_ = lean_ctor_get(v_snd_3489_, 0);
v_snd_3505_ = lean_ctor_get(v_snd_3489_, 1);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_snd_3489_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3507_ = v_snd_3489_;
v_isShared_3508_ = v_isSharedCheck_3535_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_snd_3505_);
lean_inc(v_fst_3504_);
lean_dec(v_snd_3489_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3535_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
uint8_t v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = 0;
v___x_3510_ = l_Lean_LocalDecl_value_x3f(v_val_3503_, v___x_3509_);
if (lean_obj_tag(v___x_3510_) == 1)
{
lean_object* v_val_3511_; lean_object* v___x_3512_; 
v_val_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_val_3511_);
lean_dec_ref_known(v___x_3510_, 1);
v___x_3512_ = l_Lean_LocalDecl_type(v_val_3503_);
if (lean_obj_tag(v___x_3512_) == 10)
{
lean_object* v_data_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; uint8_t v___x_3518_; 
v_data_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_data_3513_);
lean_dec_ref_known(v___x_3512_, 2);
v___x_3514_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3515_ = lean_unsigned_to_nat(2u);
v___x_3516_ = l_Lean_KVMap_getNat(v_data_3513_, v___x_3514_, v___x_3515_);
lean_dec(v_data_3513_);
v___x_3517_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3516_);
lean_dec(v___x_3516_);
v___x_3518_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3517_, v_val_3511_, v_elimTrivial_3481_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
v___x_3519_ = l_Lean_LocalDecl_fvarId(v_val_3503_);
v___x_3520_ = l_Lean_mkFVar(v___x_3519_);
v___x_3521_ = lean_array_push(v_fst_3504_, v___x_3520_);
v___x_3522_ = lean_array_push(v_snd_3505_, v_val_3511_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v___x_3522_);
lean_ctor_set(v___x_3507_, 0, v___x_3521_);
v___x_3524_ = v___x_3507_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
v_a_3495_ = v___x_3524_;
goto v___jp_3494_;
}
}
else
{
lean_object* v___x_3527_; 
lean_dec(v_val_3511_);
if (v_isShared_3508_ == 0)
{
v___x_3527_ = v___x_3507_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_fst_3504_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_snd_3505_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
v_a_3495_ = v___x_3527_;
goto v___jp_3494_;
}
}
}
else
{
lean_object* v___x_3530_; 
lean_dec_ref(v___x_3512_);
lean_dec(v_val_3511_);
if (v_isShared_3508_ == 0)
{
v___x_3530_ = v___x_3507_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_fst_3504_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_snd_3505_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
v_a_3495_ = v___x_3530_;
goto v___jp_3494_;
}
}
}
else
{
lean_object* v___x_3533_; 
lean_dec(v___x_3510_);
if (v_isShared_3508_ == 0)
{
v___x_3533_ = v___x_3507_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_fst_3504_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_snd_3505_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
v_a_3495_ = v___x_3533_;
goto v___jp_3494_;
}
}
}
}
v___jp_3494_:
{
lean_object* v___x_3497_; 
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 1, v_a_3495_);
lean_ctor_set(v___x_3491_, 0, v___x_3493_);
v___x_3497_ = v___x_3491_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_a_3495_);
v___x_3497_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
size_t v___x_3498_; size_t v___x_3499_; 
v___x_3498_ = ((size_t)1ULL);
v___x_3499_ = lean_usize_add(v_i_3484_, v___x_3498_);
v_i_3484_ = v___x_3499_;
v_b_3485_ = v___x_3497_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3538_, lean_object* v_as_3539_, lean_object* v_sz_3540_, lean_object* v_i_3541_, lean_object* v_b_3542_, lean_object* v___y_3543_){
_start:
{
uint8_t v_elimTrivial_boxed_3544_; size_t v_sz_boxed_3545_; size_t v_i_boxed_3546_; lean_object* v_res_3547_; 
v_elimTrivial_boxed_3544_ = lean_unbox(v_elimTrivial_3538_);
v_sz_boxed_3545_ = lean_unbox_usize(v_sz_3540_);
lean_dec(v_sz_3540_);
v_i_boxed_3546_ = lean_unbox_usize(v_i_3541_);
lean_dec(v_i_3541_);
v_res_3547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3544_, v_as_3539_, v_sz_boxed_3545_, v_i_boxed_3546_, v_b_3542_);
lean_dec_ref(v_as_3539_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3548_, lean_object* v_as_3549_, size_t v_sz_3550_, size_t v_i_3551_, lean_object* v_b_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
uint8_t v___x_3558_; 
v___x_3558_ = lean_usize_dec_lt(v_i_3551_, v_sz_3550_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v_b_3552_);
return v___x_3559_;
}
else
{
lean_object* v_snd_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3607_; 
v_snd_3560_ = lean_ctor_get(v_b_3552_, 1);
v_isSharedCheck_3607_ = !lean_is_exclusive(v_b_3552_);
if (v_isSharedCheck_3607_ == 0)
{
lean_object* v_unused_3608_; 
v_unused_3608_ = lean_ctor_get(v_b_3552_, 0);
lean_dec(v_unused_3608_);
v___x_3562_ = v_b_3552_;
v_isShared_3563_ = v_isSharedCheck_3607_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_snd_3560_);
lean_dec(v_b_3552_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3607_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; lean_object* v_a_3566_; lean_object* v_a_3573_; 
v___x_3564_ = lean_box(0);
v_a_3573_ = lean_array_uget_borrowed(v_as_3549_, v_i_3551_);
if (lean_obj_tag(v_a_3573_) == 0)
{
v_a_3566_ = v_snd_3560_;
goto v___jp_3565_;
}
else
{
lean_object* v_val_3574_; lean_object* v_fst_3575_; lean_object* v_snd_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3606_; 
v_val_3574_ = lean_ctor_get(v_a_3573_, 0);
v_fst_3575_ = lean_ctor_get(v_snd_3560_, 0);
v_snd_3576_ = lean_ctor_get(v_snd_3560_, 1);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_snd_3560_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3578_ = v_snd_3560_;
v_isShared_3579_ = v_isSharedCheck_3606_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_snd_3576_);
lean_inc(v_fst_3575_);
lean_dec(v_snd_3560_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3606_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
uint8_t v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = 0;
v___x_3581_ = l_Lean_LocalDecl_value_x3f(v_val_3574_, v___x_3580_);
if (lean_obj_tag(v___x_3581_) == 1)
{
lean_object* v_val_3582_; lean_object* v___x_3583_; 
v_val_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_val_3582_);
lean_dec_ref_known(v___x_3581_, 1);
v___x_3583_ = l_Lean_LocalDecl_type(v_val_3574_);
if (lean_obj_tag(v___x_3583_) == 10)
{
lean_object* v_data_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; uint8_t v___x_3588_; uint8_t v___x_3589_; 
v_data_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_data_3584_);
lean_dec_ref_known(v___x_3583_, 2);
v___x_3585_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3586_ = lean_unsigned_to_nat(2u);
v___x_3587_ = l_Lean_KVMap_getNat(v_data_3584_, v___x_3585_, v___x_3586_);
lean_dec(v_data_3584_);
v___x_3588_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3587_);
lean_dec(v___x_3587_);
v___x_3589_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3588_, v_val_3582_, v_elimTrivial_3548_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3595_; 
v___x_3590_ = l_Lean_LocalDecl_fvarId(v_val_3574_);
v___x_3591_ = l_Lean_mkFVar(v___x_3590_);
v___x_3592_ = lean_array_push(v_fst_3575_, v___x_3591_);
v___x_3593_ = lean_array_push(v_snd_3576_, v_val_3582_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 1, v___x_3593_);
lean_ctor_set(v___x_3578_, 0, v___x_3592_);
v___x_3595_ = v___x_3578_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v___x_3593_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
v_a_3566_ = v___x_3595_;
goto v___jp_3565_;
}
}
else
{
lean_object* v___x_3598_; 
lean_dec(v_val_3582_);
if (v_isShared_3579_ == 0)
{
v___x_3598_ = v___x_3578_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_fst_3575_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_snd_3576_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
v_a_3566_ = v___x_3598_;
goto v___jp_3565_;
}
}
}
else
{
lean_object* v___x_3601_; 
lean_dec_ref(v___x_3583_);
lean_dec(v_val_3582_);
if (v_isShared_3579_ == 0)
{
v___x_3601_ = v___x_3578_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_fst_3575_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v_snd_3576_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
v_a_3566_ = v___x_3601_;
goto v___jp_3565_;
}
}
}
else
{
lean_object* v___x_3604_; 
lean_dec(v___x_3581_);
if (v_isShared_3579_ == 0)
{
v___x_3604_ = v___x_3578_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_fst_3575_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v_snd_3576_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
v_a_3566_ = v___x_3604_;
goto v___jp_3565_;
}
}
}
}
v___jp_3565_:
{
lean_object* v___x_3568_; 
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 1, v_a_3566_);
lean_ctor_set(v___x_3562_, 0, v___x_3564_);
v___x_3568_ = v___x_3562_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3564_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v_a_3566_);
v___x_3568_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
size_t v___x_3569_; size_t v___x_3570_; lean_object* v___x_3571_; 
v___x_3569_ = ((size_t)1ULL);
v___x_3570_ = lean_usize_add(v_i_3551_, v___x_3569_);
v___x_3571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3548_, v_as_3549_, v_sz_3550_, v___x_3570_, v___x_3568_);
return v___x_3571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3609_, lean_object* v_as_3610_, lean_object* v_sz_3611_, lean_object* v_i_3612_, lean_object* v_b_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
uint8_t v_elimTrivial_boxed_3619_; size_t v_sz_boxed_3620_; size_t v_i_boxed_3621_; lean_object* v_res_3622_; 
v_elimTrivial_boxed_3619_ = lean_unbox(v_elimTrivial_3609_);
v_sz_boxed_3620_ = lean_unbox_usize(v_sz_3611_);
lean_dec(v_sz_3611_);
v_i_boxed_3621_ = lean_unbox_usize(v_i_3612_);
lean_dec(v_i_3612_);
v_res_3622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3619_, v_as_3610_, v_sz_boxed_3620_, v_i_boxed_3621_, v_b_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec_ref(v_as_3610_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3623_, uint8_t v_elimTrivial_3624_, lean_object* v_n_3625_, lean_object* v_b_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
if (lean_obj_tag(v_n_3625_) == 0)
{
lean_object* v_cs_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; size_t v_sz_3635_; size_t v___x_3636_; lean_object* v___x_3637_; 
v_cs_3632_ = lean_ctor_get(v_n_3625_, 0);
v___x_3633_ = lean_box(0);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set(v___x_3634_, 1, v_b_3626_);
v_sz_3635_ = lean_array_size(v_cs_3632_);
v___x_3636_ = ((size_t)0ULL);
v___x_3637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3623_, v_elimTrivial_3624_, v_cs_3632_, v_sz_3635_, v___x_3636_, v___x_3634_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3652_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3640_ = v___x_3637_;
v_isShared_3641_ = v_isSharedCheck_3652_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3652_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v_fst_3642_; 
v_fst_3642_ = lean_ctor_get(v_a_3638_, 0);
if (lean_obj_tag(v_fst_3642_) == 0)
{
lean_object* v_snd_3643_; lean_object* v___x_3644_; lean_object* v___x_3646_; 
v_snd_3643_ = lean_ctor_get(v_a_3638_, 1);
lean_inc(v_snd_3643_);
lean_dec(v_a_3638_);
v___x_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3644_, 0, v_snd_3643_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3644_);
v___x_3646_ = v___x_3640_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
else
{
lean_object* v_val_3648_; lean_object* v___x_3650_; 
lean_inc_ref(v_fst_3642_);
lean_dec(v_a_3638_);
v_val_3648_ = lean_ctor_get(v_fst_3642_, 0);
lean_inc(v_val_3648_);
lean_dec_ref_known(v_fst_3642_, 1);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v_val_3648_);
v___x_3650_ = v___x_3640_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_val_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
v_a_3653_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3637_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3637_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
else
{
lean_object* v_vs_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; size_t v_sz_3664_; size_t v___x_3665_; lean_object* v___x_3666_; 
v_vs_3661_ = lean_ctor_get(v_n_3625_, 0);
v___x_3662_ = lean_box(0);
v___x_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
lean_ctor_set(v___x_3663_, 1, v_b_3626_);
v_sz_3664_ = lean_array_size(v_vs_3661_);
v___x_3665_ = ((size_t)0ULL);
v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3624_, v_vs_3661_, v_sz_3664_, v___x_3665_, v___x_3663_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3681_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3669_ = v___x_3666_;
v_isShared_3670_ = v_isSharedCheck_3681_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3681_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_fst_3671_; 
v_fst_3671_ = lean_ctor_get(v_a_3667_, 0);
if (lean_obj_tag(v_fst_3671_) == 0)
{
lean_object* v_snd_3672_; lean_object* v___x_3673_; lean_object* v___x_3675_; 
v_snd_3672_ = lean_ctor_get(v_a_3667_, 1);
lean_inc(v_snd_3672_);
lean_dec(v_a_3667_);
v___x_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3673_, 0, v_snd_3672_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3673_);
v___x_3675_ = v___x_3669_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3673_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
else
{
lean_object* v_val_3677_; lean_object* v___x_3679_; 
lean_inc_ref(v_fst_3671_);
lean_dec(v_a_3667_);
v_val_3677_ = lean_ctor_get(v_fst_3671_, 0);
lean_inc(v_val_3677_);
lean_dec_ref_known(v_fst_3671_, 1);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v_val_3677_);
v___x_3679_ = v___x_3669_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_val_3677_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
v_a_3682_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3666_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3666_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3690_, uint8_t v_elimTrivial_3691_, lean_object* v_as_3692_, size_t v_sz_3693_, size_t v_i_3694_, lean_object* v_b_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
uint8_t v___x_3701_; 
v___x_3701_ = lean_usize_dec_lt(v_i_3694_, v_sz_3693_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3702_, 0, v_b_3695_);
return v___x_3702_;
}
else
{
lean_object* v_snd_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3737_; 
v_snd_3703_ = lean_ctor_get(v_b_3695_, 1);
v_isSharedCheck_3737_ = !lean_is_exclusive(v_b_3695_);
if (v_isSharedCheck_3737_ == 0)
{
lean_object* v_unused_3738_; 
v_unused_3738_ = lean_ctor_get(v_b_3695_, 0);
lean_dec(v_unused_3738_);
v___x_3705_ = v_b_3695_;
v_isShared_3706_ = v_isSharedCheck_3737_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_snd_3703_);
lean_dec(v_b_3695_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3737_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v_a_3707_; lean_object* v___x_3708_; 
v_a_3707_ = lean_array_uget_borrowed(v_as_3692_, v_i_3694_);
lean_inc(v_snd_3703_);
v___x_3708_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3690_, v_elimTrivial_3691_, v_a_3707_, v_snd_3703_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3728_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3711_ = v___x_3708_;
v_isShared_3712_ = v_isSharedCheck_3728_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3708_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3728_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
if (lean_obj_tag(v_a_3709_) == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3715_; 
v___x_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3713_, 0, v_a_3709_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v___x_3713_);
v___x_3715_ = v___x_3705_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3713_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_snd_3703_);
v___x_3715_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3717_; 
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 0, v___x_3715_);
v___x_3717_ = v___x_3711_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3715_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3721_; lean_object* v___x_3723_; 
lean_del_object(v___x_3711_);
lean_dec(v_snd_3703_);
v_a_3720_ = lean_ctor_get(v_a_3709_, 0);
lean_inc(v_a_3720_);
lean_dec_ref_known(v_a_3709_, 1);
v___x_3721_ = lean_box(0);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 1, v_a_3720_);
lean_ctor_set(v___x_3705_, 0, v___x_3721_);
v___x_3723_ = v___x_3705_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_a_3720_);
v___x_3723_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
size_t v___x_3724_; size_t v___x_3725_; 
v___x_3724_ = ((size_t)1ULL);
v___x_3725_ = lean_usize_add(v_i_3694_, v___x_3724_);
v_i_3694_ = v___x_3725_;
v_b_3695_ = v___x_3723_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_del_object(v___x_3705_);
lean_dec(v_snd_3703_);
v_a_3729_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3708_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3708_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3739_, lean_object* v_elimTrivial_3740_, lean_object* v_as_3741_, lean_object* v_sz_3742_, lean_object* v_i_3743_, lean_object* v_b_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
uint8_t v_elimTrivial_boxed_3750_; size_t v_sz_boxed_3751_; size_t v_i_boxed_3752_; lean_object* v_res_3753_; 
v_elimTrivial_boxed_3750_ = lean_unbox(v_elimTrivial_3740_);
v_sz_boxed_3751_ = lean_unbox_usize(v_sz_3742_);
lean_dec(v_sz_3742_);
v_i_boxed_3752_ = lean_unbox_usize(v_i_3743_);
lean_dec(v_i_3743_);
v_res_3753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3739_, v_elimTrivial_boxed_3750_, v_as_3741_, v_sz_boxed_3751_, v_i_boxed_3752_, v_b_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec_ref(v_as_3741_);
lean_dec_ref(v_init_3739_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3754_, lean_object* v_elimTrivial_3755_, lean_object* v_n_3756_, lean_object* v_b_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
uint8_t v_elimTrivial_boxed_3763_; lean_object* v_res_3764_; 
v_elimTrivial_boxed_3763_ = lean_unbox(v_elimTrivial_3755_);
v_res_3764_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3754_, v_elimTrivial_boxed_3763_, v_n_3756_, v_b_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec_ref(v_n_3756_);
lean_dec_ref(v_init_3754_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3765_, lean_object* v_t_3766_, lean_object* v_init_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v_root_3773_; lean_object* v_tail_3774_; lean_object* v___x_3775_; 
v_root_3773_ = lean_ctor_get(v_t_3766_, 0);
v_tail_3774_ = lean_ctor_get(v_t_3766_, 1);
lean_inc_ref(v_init_3767_);
v___x_3775_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3767_, v_elimTrivial_3765_, v_root_3773_, v_init_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
lean_dec_ref(v_init_3767_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3812_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3812_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3812_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
if (lean_obj_tag(v_a_3776_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3782_; 
v_a_3780_ = lean_ctor_get(v_a_3776_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v_a_3776_, 1);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 0, v_a_3780_);
v___x_3782_ = v___x_3778_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3780_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; size_t v_sz_3787_; size_t v___x_3788_; lean_object* v___x_3789_; 
lean_del_object(v___x_3778_);
v_a_3784_ = lean_ctor_get(v_a_3776_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v_a_3776_, 1);
v___x_3785_ = lean_box(0);
v___x_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
lean_ctor_set(v___x_3786_, 1, v_a_3784_);
v_sz_3787_ = lean_array_size(v_tail_3774_);
v___x_3788_ = ((size_t)0ULL);
v___x_3789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3765_, v_tail_3774_, v_sz_3787_, v___x_3788_, v___x_3786_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3803_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3792_ = v___x_3789_;
v_isShared_3793_ = v_isSharedCheck_3803_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3789_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3803_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v_fst_3794_; 
v_fst_3794_ = lean_ctor_get(v_a_3790_, 0);
if (lean_obj_tag(v_fst_3794_) == 0)
{
lean_object* v_snd_3795_; lean_object* v___x_3797_; 
v_snd_3795_ = lean_ctor_get(v_a_3790_, 1);
lean_inc(v_snd_3795_);
lean_dec(v_a_3790_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v_snd_3795_);
v___x_3797_ = v___x_3792_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_snd_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
else
{
lean_object* v_val_3799_; lean_object* v___x_3801_; 
lean_inc_ref(v_fst_3794_);
lean_dec(v_a_3790_);
v_val_3799_ = lean_ctor_get(v_fst_3794_, 0);
lean_inc(v_val_3799_);
lean_dec_ref_known(v_fst_3794_, 1);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v_val_3799_);
v___x_3801_ = v___x_3792_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_val_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
v_a_3804_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3789_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3789_);
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
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
v_a_3813_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3775_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3775_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_3821_, lean_object* v_t_3822_, lean_object* v_init_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
uint8_t v_elimTrivial_boxed_3829_; lean_object* v_res_3830_; 
v_elimTrivial_boxed_3829_ = lean_unbox(v_elimTrivial_3821_);
v_res_3830_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_3829_, v_t_3822_, v_init_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec_ref(v_t_3822_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_3831_, size_t v_sz_3832_, size_t v_i_3833_, lean_object* v_b_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
uint8_t v___x_3840_; 
v___x_3840_ = lean_usize_dec_lt(v_i_3833_, v_sz_3832_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3841_, 0, v_b_3834_);
return v___x_3841_;
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v_a_3842_ = lean_array_uget_borrowed(v_as_3831_, v_i_3833_);
v___x_3843_ = l_Lean_Expr_fvarId_x21(v_a_3842_);
v___x_3844_ = l_Lean_MVarId_tryClear(v_b_3834_, v___x_3843_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; size_t v___x_3846_; size_t v___x_3847_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
v___x_3846_ = ((size_t)1ULL);
v___x_3847_ = lean_usize_add(v_i_3833_, v___x_3846_);
v_i_3833_ = v___x_3847_;
v_b_3834_ = v_a_3845_;
goto _start;
}
else
{
return v___x_3844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_3849_, lean_object* v_sz_3850_, lean_object* v_i_3851_, lean_object* v_b_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
size_t v_sz_boxed_3858_; size_t v_i_boxed_3859_; lean_object* v_res_3860_; 
v_sz_boxed_3858_ = lean_unbox_usize(v_sz_3850_);
lean_dec(v_sz_3850_);
v_i_boxed_3859_ = lean_unbox_usize(v_i_3851_);
lean_dec(v_i_3851_);
v_res_3860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3849_, v_sz_boxed_3858_, v_i_boxed_3859_, v_b_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec_ref(v_as_3849_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_3861_, lean_object* v_x_3862_, lean_object* v_x_3863_, lean_object* v_x_3864_){
_start:
{
lean_object* v_ks_3865_; lean_object* v_vs_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3890_; 
v_ks_3865_ = lean_ctor_get(v_x_3861_, 0);
v_vs_3866_ = lean_ctor_get(v_x_3861_, 1);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_x_3861_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3868_ = v_x_3861_;
v_isShared_3869_ = v_isSharedCheck_3890_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_vs_3866_);
lean_inc(v_ks_3865_);
lean_dec(v_x_3861_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3890_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; uint8_t v___x_3871_; 
v___x_3870_ = lean_array_get_size(v_ks_3865_);
v___x_3871_ = lean_nat_dec_lt(v_x_3862_, v___x_3870_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3875_; 
lean_dec(v_x_3862_);
v___x_3872_ = lean_array_push(v_ks_3865_, v_x_3863_);
v___x_3873_ = lean_array_push(v_vs_3866_, v_x_3864_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 1, v___x_3873_);
lean_ctor_set(v___x_3868_, 0, v___x_3872_);
v___x_3875_ = v___x_3868_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3872_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v___x_3873_);
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
lean_object* v_k_x27_3877_; uint8_t v___x_3878_; 
v_k_x27_3877_ = lean_array_fget_borrowed(v_ks_3865_, v_x_3862_);
v___x_3878_ = l_Lean_instBEqMVarId_beq(v_x_3863_, v_k_x27_3877_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3880_; 
if (v_isShared_3869_ == 0)
{
v___x_3880_ = v___x_3868_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_ks_3865_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_vs_3866_);
v___x_3880_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = lean_unsigned_to_nat(1u);
v___x_3882_ = lean_nat_add(v_x_3862_, v___x_3881_);
lean_dec(v_x_3862_);
v_x_3861_ = v___x_3880_;
v_x_3862_ = v___x_3882_;
goto _start;
}
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3885_ = lean_array_fset(v_ks_3865_, v_x_3862_, v_x_3863_);
v___x_3886_ = lean_array_fset(v_vs_3866_, v_x_3862_, v_x_3864_);
lean_dec(v_x_3862_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 1, v___x_3886_);
lean_ctor_set(v___x_3868_, 0, v___x_3885_);
v___x_3888_ = v___x_3868_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v___x_3886_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_3891_, lean_object* v_k_3892_, lean_object* v_v_3893_){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = lean_unsigned_to_nat(0u);
v___x_3895_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_3891_, v___x_3894_, v_k_3892_, v_v_3893_);
return v___x_3895_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_3897_, size_t v_x_3898_, size_t v_x_3899_, lean_object* v_x_3900_, lean_object* v_x_3901_){
_start:
{
if (lean_obj_tag(v_x_3897_) == 0)
{
lean_object* v_es_3902_; size_t v___x_3903_; size_t v___x_3904_; lean_object* v_j_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v_es_3902_ = lean_ctor_get(v_x_3897_, 0);
v___x_3903_ = ((size_t)31ULL);
v___x_3904_ = lean_usize_land(v_x_3898_, v___x_3903_);
v_j_3905_ = lean_usize_to_nat(v___x_3904_);
v___x_3906_ = lean_array_get_size(v_es_3902_);
v___x_3907_ = lean_nat_dec_lt(v_j_3905_, v___x_3906_);
if (v___x_3907_ == 0)
{
lean_dec(v_j_3905_);
lean_dec(v_x_3901_);
lean_dec(v_x_3900_);
return v_x_3897_;
}
else
{
lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3946_; 
lean_inc_ref(v_es_3902_);
v_isSharedCheck_3946_ = !lean_is_exclusive(v_x_3897_);
if (v_isSharedCheck_3946_ == 0)
{
lean_object* v_unused_3947_; 
v_unused_3947_ = lean_ctor_get(v_x_3897_, 0);
lean_dec(v_unused_3947_);
v___x_3909_ = v_x_3897_;
v_isShared_3910_ = v_isSharedCheck_3946_;
goto v_resetjp_3908_;
}
else
{
lean_dec(v_x_3897_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3946_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v_v_3911_; lean_object* v___x_3912_; lean_object* v_xs_x27_3913_; lean_object* v___y_3915_; 
v_v_3911_ = lean_array_fget(v_es_3902_, v_j_3905_);
v___x_3912_ = lean_box(0);
v_xs_x27_3913_ = lean_array_fset(v_es_3902_, v_j_3905_, v___x_3912_);
switch(lean_obj_tag(v_v_3911_))
{
case 0:
{
lean_object* v_key_3920_; lean_object* v_val_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3931_; 
v_key_3920_ = lean_ctor_get(v_v_3911_, 0);
v_val_3921_ = lean_ctor_get(v_v_3911_, 1);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_v_3911_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3923_ = v_v_3911_;
v_isShared_3924_ = v_isSharedCheck_3931_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_val_3921_);
lean_inc(v_key_3920_);
lean_dec(v_v_3911_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3931_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
uint8_t v___x_3925_; 
v___x_3925_ = l_Lean_instBEqMVarId_beq(v_x_3900_, v_key_3920_);
if (v___x_3925_ == 0)
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_del_object(v___x_3923_);
v___x_3926_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3920_, v_val_3921_, v_x_3900_, v_x_3901_);
v___x_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
v___y_3915_ = v___x_3927_;
goto v___jp_3914_;
}
else
{
lean_object* v___x_3929_; 
lean_dec(v_val_3921_);
lean_dec(v_key_3920_);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 1, v_x_3901_);
lean_ctor_set(v___x_3923_, 0, v_x_3900_);
v___x_3929_ = v___x_3923_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_x_3900_);
lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_x_3901_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
v___y_3915_ = v___x_3929_;
goto v___jp_3914_;
}
}
}
}
case 1:
{
lean_object* v_node_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3944_; 
v_node_3932_ = lean_ctor_get(v_v_3911_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_v_3911_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3934_ = v_v_3911_;
v_isShared_3935_ = v_isSharedCheck_3944_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_node_3932_);
lean_dec(v_v_3911_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3944_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
size_t v___x_3936_; size_t v___x_3937_; size_t v___x_3938_; size_t v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3942_; 
v___x_3936_ = ((size_t)5ULL);
v___x_3937_ = lean_usize_shift_right(v_x_3898_, v___x_3936_);
v___x_3938_ = ((size_t)1ULL);
v___x_3939_ = lean_usize_add(v_x_3899_, v___x_3938_);
v___x_3940_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_3932_, v___x_3937_, v___x_3939_, v_x_3900_, v_x_3901_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 0, v___x_3940_);
v___x_3942_ = v___x_3934_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
v___y_3915_ = v___x_3942_;
goto v___jp_3914_;
}
}
}
default: 
{
lean_object* v___x_3945_; 
v___x_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3945_, 0, v_x_3900_);
lean_ctor_set(v___x_3945_, 1, v_x_3901_);
v___y_3915_ = v___x_3945_;
goto v___jp_3914_;
}
}
v___jp_3914_:
{
lean_object* v___x_3916_; lean_object* v___x_3918_; 
v___x_3916_ = lean_array_fset(v_xs_x27_3913_, v_j_3905_, v___y_3915_);
lean_dec(v_j_3905_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3916_);
v___x_3918_ = v___x_3909_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
}
else
{
lean_object* v_ks_3948_; lean_object* v_vs_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3967_; 
v_ks_3948_ = lean_ctor_get(v_x_3897_, 0);
v_vs_3949_ = lean_ctor_get(v_x_3897_, 1);
v_isSharedCheck_3967_ = !lean_is_exclusive(v_x_3897_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3951_ = v_x_3897_;
v_isShared_3952_ = v_isSharedCheck_3967_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_vs_3949_);
lean_inc(v_ks_3948_);
lean_dec(v_x_3897_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3967_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_ks_3948_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_vs_3949_);
v___x_3954_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
lean_object* v_newNode_3955_; size_t v___x_3956_; uint8_t v___x_3957_; 
v_newNode_3955_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_3954_, v_x_3900_, v_x_3901_);
v___x_3956_ = ((size_t)7ULL);
v___x_3957_ = lean_usize_dec_le(v___x_3956_, v_x_3899_);
if (v___x_3957_ == 0)
{
lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v___x_3958_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3955_);
v___x_3959_ = lean_unsigned_to_nat(4u);
v___x_3960_ = lean_nat_dec_lt(v___x_3958_, v___x_3959_);
lean_dec(v___x_3958_);
if (v___x_3960_ == 0)
{
lean_object* v_ks_3961_; lean_object* v_vs_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v_ks_3961_ = lean_ctor_get(v_newNode_3955_, 0);
lean_inc_ref(v_ks_3961_);
v_vs_3962_ = lean_ctor_get(v_newNode_3955_, 1);
lean_inc_ref(v_vs_3962_);
lean_dec_ref(v_newNode_3955_);
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_3965_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3899_, v_ks_3961_, v_vs_3962_, v___x_3963_, v___x_3964_);
lean_dec_ref(v_vs_3962_);
lean_dec_ref(v_ks_3961_);
return v___x_3965_;
}
else
{
return v_newNode_3955_;
}
}
else
{
return v_newNode_3955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_3968_, lean_object* v_keys_3969_, lean_object* v_vals_3970_, lean_object* v_i_3971_, lean_object* v_entries_3972_){
_start:
{
lean_object* v___x_3973_; uint8_t v___x_3974_; 
v___x_3973_ = lean_array_get_size(v_keys_3969_);
v___x_3974_ = lean_nat_dec_lt(v_i_3971_, v___x_3973_);
if (v___x_3974_ == 0)
{
lean_dec(v_i_3971_);
return v_entries_3972_;
}
else
{
lean_object* v_k_3975_; lean_object* v_v_3976_; uint64_t v___x_3977_; size_t v_h_3978_; size_t v___x_3979_; lean_object* v___x_3980_; size_t v___x_3981_; size_t v___x_3982_; size_t v___x_3983_; size_t v_h_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_k_3975_ = lean_array_fget_borrowed(v_keys_3969_, v_i_3971_);
v_v_3976_ = lean_array_fget_borrowed(v_vals_3970_, v_i_3971_);
v___x_3977_ = l_Lean_instHashableMVarId_hash(v_k_3975_);
v_h_3978_ = lean_uint64_to_usize(v___x_3977_);
v___x_3979_ = ((size_t)5ULL);
v___x_3980_ = lean_unsigned_to_nat(1u);
v___x_3981_ = ((size_t)1ULL);
v___x_3982_ = lean_usize_sub(v_depth_3968_, v___x_3981_);
v___x_3983_ = lean_usize_mul(v___x_3979_, v___x_3982_);
v_h_3984_ = lean_usize_shift_right(v_h_3978_, v___x_3983_);
v___x_3985_ = lean_nat_add(v_i_3971_, v___x_3980_);
lean_dec(v_i_3971_);
lean_inc(v_v_3976_);
lean_inc(v_k_3975_);
v___x_3986_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_3972_, v_h_3984_, v_depth_3968_, v_k_3975_, v_v_3976_);
v_i_3971_ = v___x_3985_;
v_entries_3972_ = v___x_3986_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_3988_, lean_object* v_keys_3989_, lean_object* v_vals_3990_, lean_object* v_i_3991_, lean_object* v_entries_3992_){
_start:
{
size_t v_depth_boxed_3993_; lean_object* v_res_3994_; 
v_depth_boxed_3993_ = lean_unbox_usize(v_depth_3988_);
lean_dec(v_depth_3988_);
v_res_3994_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_3993_, v_keys_3989_, v_vals_3990_, v_i_3991_, v_entries_3992_);
lean_dec_ref(v_vals_3990_);
lean_dec_ref(v_keys_3989_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_3995_, lean_object* v_x_3996_, lean_object* v_x_3997_, lean_object* v_x_3998_, lean_object* v_x_3999_){
_start:
{
size_t v_x_7803__boxed_4000_; size_t v_x_7804__boxed_4001_; lean_object* v_res_4002_; 
v_x_7803__boxed_4000_ = lean_unbox_usize(v_x_3996_);
lean_dec(v_x_3996_);
v_x_7804__boxed_4001_ = lean_unbox_usize(v_x_3997_);
lean_dec(v_x_3997_);
v_res_4002_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_3995_, v_x_7803__boxed_4000_, v_x_7804__boxed_4001_, v_x_3998_, v_x_3999_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_4003_, lean_object* v_x_4004_, lean_object* v_x_4005_){
_start:
{
uint64_t v___x_4006_; size_t v___x_4007_; size_t v___x_4008_; lean_object* v___x_4009_; 
v___x_4006_ = l_Lean_instHashableMVarId_hash(v_x_4004_);
v___x_4007_ = lean_uint64_to_usize(v___x_4006_);
v___x_4008_ = ((size_t)1ULL);
v___x_4009_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4003_, v___x_4007_, v___x_4008_, v_x_4004_, v_x_4005_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4010_, lean_object* v_val_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v___x_4014_; lean_object* v_mctx_4015_; lean_object* v_cache_4016_; lean_object* v_zetaDeltaFVarIds_4017_; lean_object* v_postponed_4018_; lean_object* v_diag_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4048_; 
v___x_4014_ = lean_st_ref_take(v___y_4012_);
v_mctx_4015_ = lean_ctor_get(v___x_4014_, 0);
v_cache_4016_ = lean_ctor_get(v___x_4014_, 1);
v_zetaDeltaFVarIds_4017_ = lean_ctor_get(v___x_4014_, 2);
v_postponed_4018_ = lean_ctor_get(v___x_4014_, 3);
v_diag_4019_ = lean_ctor_get(v___x_4014_, 4);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4021_ = v___x_4014_;
v_isShared_4022_ = v_isSharedCheck_4048_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_diag_4019_);
lean_inc(v_postponed_4018_);
lean_inc(v_zetaDeltaFVarIds_4017_);
lean_inc(v_cache_4016_);
lean_inc(v_mctx_4015_);
lean_dec(v___x_4014_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4048_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v_depth_4023_; lean_object* v_levelAssignDepth_4024_; lean_object* v_lmvarCounter_4025_; lean_object* v_mvarCounter_4026_; lean_object* v_lDecls_4027_; lean_object* v_decls_4028_; lean_object* v_userNames_4029_; lean_object* v_lAssignment_4030_; lean_object* v_eAssignment_4031_; lean_object* v_dAssignment_4032_; lean_object* v_instanceTypedMVars_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4047_; 
v_depth_4023_ = lean_ctor_get(v_mctx_4015_, 0);
v_levelAssignDepth_4024_ = lean_ctor_get(v_mctx_4015_, 1);
v_lmvarCounter_4025_ = lean_ctor_get(v_mctx_4015_, 2);
v_mvarCounter_4026_ = lean_ctor_get(v_mctx_4015_, 3);
v_lDecls_4027_ = lean_ctor_get(v_mctx_4015_, 4);
v_decls_4028_ = lean_ctor_get(v_mctx_4015_, 5);
v_userNames_4029_ = lean_ctor_get(v_mctx_4015_, 6);
v_lAssignment_4030_ = lean_ctor_get(v_mctx_4015_, 7);
v_eAssignment_4031_ = lean_ctor_get(v_mctx_4015_, 8);
v_dAssignment_4032_ = lean_ctor_get(v_mctx_4015_, 9);
v_instanceTypedMVars_4033_ = lean_ctor_get(v_mctx_4015_, 10);
v_isSharedCheck_4047_ = !lean_is_exclusive(v_mctx_4015_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4035_ = v_mctx_4015_;
v_isShared_4036_ = v_isSharedCheck_4047_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_instanceTypedMVars_4033_);
lean_inc(v_dAssignment_4032_);
lean_inc(v_eAssignment_4031_);
lean_inc(v_lAssignment_4030_);
lean_inc(v_userNames_4029_);
lean_inc(v_decls_4028_);
lean_inc(v_lDecls_4027_);
lean_inc(v_mvarCounter_4026_);
lean_inc(v_lmvarCounter_4025_);
lean_inc(v_levelAssignDepth_4024_);
lean_inc(v_depth_4023_);
lean_dec(v_mctx_4015_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4047_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4037_; lean_object* v___x_4039_; 
v___x_4037_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4031_, v_mvarId_4010_, v_val_4011_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 8, v___x_4037_);
v___x_4039_ = v___x_4035_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_depth_4023_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v_levelAssignDepth_4024_);
lean_ctor_set(v_reuseFailAlloc_4046_, 2, v_lmvarCounter_4025_);
lean_ctor_set(v_reuseFailAlloc_4046_, 3, v_mvarCounter_4026_);
lean_ctor_set(v_reuseFailAlloc_4046_, 4, v_lDecls_4027_);
lean_ctor_set(v_reuseFailAlloc_4046_, 5, v_decls_4028_);
lean_ctor_set(v_reuseFailAlloc_4046_, 6, v_userNames_4029_);
lean_ctor_set(v_reuseFailAlloc_4046_, 7, v_lAssignment_4030_);
lean_ctor_set(v_reuseFailAlloc_4046_, 8, v___x_4037_);
lean_ctor_set(v_reuseFailAlloc_4046_, 9, v_dAssignment_4032_);
lean_ctor_set(v_reuseFailAlloc_4046_, 10, v_instanceTypedMVars_4033_);
v___x_4039_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
lean_object* v___x_4041_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v___x_4039_);
v___x_4041_ = v___x_4021_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v_cache_4016_);
lean_ctor_set(v_reuseFailAlloc_4045_, 2, v_zetaDeltaFVarIds_4017_);
lean_ctor_set(v_reuseFailAlloc_4045_, 3, v_postponed_4018_);
lean_ctor_set(v_reuseFailAlloc_4045_, 4, v_diag_4019_);
v___x_4041_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = lean_st_ref_put(v___y_4012_, v___x_4041_);
v___x_4043_ = lean_box(0);
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
return v___x_4044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4049_, lean_object* v_val_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4049_, v_val_4050_, v___y_4051_);
lean_dec(v___y_4051_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4056_, uint8_t v_elimTrivial_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; 
lean_inc(v_mvar_4056_);
v___x_4063_ = l_Lean_MVarId_getType(v_mvar_4056_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v___x_4065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4066_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4064_, v___x_4065_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v_fst_4068_; lean_object* v_snd_4069_; lean_object* v_lctx_4070_; lean_object* v___x_4071_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 1);
v_fst_4068_ = lean_ctor_get(v_a_4067_, 0);
lean_inc(v_fst_4068_);
v_snd_4069_ = lean_ctor_get(v_a_4067_, 1);
lean_inc(v_snd_4069_);
lean_dec(v_a_4067_);
v_lctx_4070_ = lean_ctor_get(v___y_4058_, 2);
lean_inc_ref(v_lctx_4070_);
v___x_4071_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4070_, v_snd_4069_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4073_; lean_object* v_decls_4074_; lean_object* v___x_4075_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
v___x_4073_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4074_ = lean_ctor_get(v_a_4072_, 1);
lean_inc_ref(v_decls_4074_);
lean_dec(v_a_4072_);
v___x_4075_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4057_, v_decls_4074_, v___x_4073_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
lean_dec_ref(v_decls_4074_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v_fst_4077_; lean_object* v_snd_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___x_4075_, 1);
v_fst_4077_ = lean_ctor_get(v_a_4076_, 0);
lean_inc(v_fst_4077_);
v_snd_4078_ = lean_ctor_get(v_a_4076_, 1);
lean_inc(v_snd_4078_);
lean_dec(v_a_4076_);
v___x_4079_ = l_Lean_Expr_replaceFVars(v_fst_4068_, v_fst_4077_, v_snd_4078_);
lean_dec(v_snd_4078_);
lean_dec(v_fst_4068_);
v___x_4080_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4079_, v_elimTrivial_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v___x_4082_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4080_, 1);
lean_inc(v_mvar_4056_);
v___x_4082_ = l_Lean_MVarId_getTag(v_mvar_4056_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4084_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4082_, 1);
v___x_4084_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4081_, v_a_4083_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; size_t v_sz_4088_; size_t v___x_4089_; lean_object* v___x_4090_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc_n(v_a_4085_, 2);
lean_dec_ref_known(v___x_4084_, 1);
v___x_4086_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4056_, v_a_4085_, v___y_4059_);
lean_dec_ref(v___x_4086_);
v___x_4087_ = l_Lean_Expr_mvarId_x21(v_a_4085_);
lean_dec(v_a_4085_);
v_sz_4088_ = lean_array_size(v_fst_4077_);
v___x_4089_ = ((size_t)0ULL);
v___x_4090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4077_, v_sz_4088_, v___x_4089_, v___x_4087_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
lean_dec_ref(v___y_4058_);
lean_dec(v_fst_4077_);
return v___x_4090_;
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
lean_dec(v_fst_4077_);
lean_dec_ref(v___y_4058_);
lean_dec(v_mvar_4056_);
v_a_4091_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4084_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4084_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec(v_a_4081_);
lean_dec(v_fst_4077_);
lean_dec_ref(v___y_4058_);
lean_dec(v_mvar_4056_);
v_a_4099_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4082_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4082_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec(v_fst_4077_);
lean_dec_ref(v___y_4058_);
lean_dec(v_mvar_4056_);
v_a_4107_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4080_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4080_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_dec(v_fst_4068_);
lean_dec_ref(v___y_4058_);
lean_dec(v_mvar_4056_);
v_a_4115_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4075_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4075_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec(v_fst_4068_);
lean_dec_ref(v___y_4058_);
lean_dec(v_mvar_4056_);
v_a_4123_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4071_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4071_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
else
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
lean_dec_ref(v___y_4058_);
lean_dec(v_mvar_4056_);
v_a_4131_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4066_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4066_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
else
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
lean_dec_ref(v___y_4058_);
lean_dec(v_mvar_4056_);
v_a_4139_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4063_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4063_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4147_, lean_object* v_elimTrivial_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
uint8_t v_elimTrivial_boxed_4154_; lean_object* v_res_4155_; 
v_elimTrivial_boxed_4154_ = lean_unbox(v_elimTrivial_4148_);
v_res_4155_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4147_, v_elimTrivial_boxed_4154_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4156_, uint8_t v_elimTrivial_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v___x_4163_; lean_object* v___f_4164_; lean_object* v___x_4165_; 
v___x_4163_ = lean_box(v_elimTrivial_4157_);
lean_inc(v_mvar_4156_);
v___f_4164_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4164_, 0, v_mvar_4156_);
lean_closure_set(v___f_4164_, 1, v___x_4163_);
v___x_4165_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4156_, v___f_4164_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4166_, lean_object* v_elimTrivial_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_){
_start:
{
uint8_t v_elimTrivial_boxed_4173_; lean_object* v_res_4174_; 
v_elimTrivial_boxed_4173_ = lean_unbox(v_elimTrivial_4167_);
v_res_4174_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4166_, v_elimTrivial_boxed_4173_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4175_, lean_object* v_val_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4175_, v_val_4176_, v___y_4178_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4183_, lean_object* v_val_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4183_, v_val_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4191_, lean_object* v_x_4192_, lean_object* v_x_4193_, lean_object* v_x_4194_){
_start:
{
lean_object* v___x_4195_; 
v___x_4195_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4192_, v_x_4193_, v_x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4196_, lean_object* v_as_4197_, size_t v_sz_4198_, size_t v_i_4199_, lean_object* v_b_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4196_, v_as_4197_, v_sz_4198_, v_i_4199_, v_b_4200_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4207_, lean_object* v_as_4208_, lean_object* v_sz_4209_, lean_object* v_i_4210_, lean_object* v_b_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
uint8_t v_elimTrivial_boxed_4217_; size_t v_sz_boxed_4218_; size_t v_i_boxed_4219_; lean_object* v_res_4220_; 
v_elimTrivial_boxed_4217_ = lean_unbox(v_elimTrivial_4207_);
v_sz_boxed_4218_ = lean_unbox_usize(v_sz_4209_);
lean_dec(v_sz_4209_);
v_i_boxed_4219_ = lean_unbox_usize(v_i_4210_);
lean_dec(v_i_4210_);
v_res_4220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4217_, v_as_4208_, v_sz_boxed_4218_, v_i_boxed_4219_, v_b_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec_ref(v_as_4208_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4221_, lean_object* v_x_4222_, size_t v_x_4223_, size_t v_x_4224_, lean_object* v_x_4225_, lean_object* v_x_4226_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4222_, v_x_4223_, v_x_4224_, v_x_4225_, v_x_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4228_, lean_object* v_x_4229_, lean_object* v_x_4230_, lean_object* v_x_4231_, lean_object* v_x_4232_, lean_object* v_x_4233_){
_start:
{
size_t v_x_8249__boxed_4234_; size_t v_x_8250__boxed_4235_; lean_object* v_res_4236_; 
v_x_8249__boxed_4234_ = lean_unbox_usize(v_x_4230_);
lean_dec(v_x_4230_);
v_x_8250__boxed_4235_ = lean_unbox_usize(v_x_4231_);
lean_dec(v_x_4231_);
v_res_4236_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4228_, v_x_4229_, v_x_8249__boxed_4234_, v_x_8250__boxed_4235_, v_x_4232_, v_x_4233_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4237_, lean_object* v_as_4238_, size_t v_sz_4239_, size_t v_i_4240_, lean_object* v_b_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4237_, v_as_4238_, v_sz_4239_, v_i_4240_, v_b_4241_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4248_, lean_object* v_as_4249_, lean_object* v_sz_4250_, lean_object* v_i_4251_, lean_object* v_b_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
uint8_t v_elimTrivial_boxed_4258_; size_t v_sz_boxed_4259_; size_t v_i_boxed_4260_; lean_object* v_res_4261_; 
v_elimTrivial_boxed_4258_ = lean_unbox(v_elimTrivial_4248_);
v_sz_boxed_4259_ = lean_unbox_usize(v_sz_4250_);
lean_dec(v_sz_4250_);
v_i_boxed_4260_ = lean_unbox_usize(v_i_4251_);
lean_dec(v_i_4251_);
v_res_4261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4258_, v_as_4249_, v_sz_boxed_4259_, v_i_boxed_4260_, v_b_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec_ref(v_as_4249_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4262_, lean_object* v_n_4263_, lean_object* v_k_4264_, lean_object* v_v_4265_){
_start:
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4263_, v_k_4264_, v_v_4265_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4267_, size_t v_depth_4268_, lean_object* v_keys_4269_, lean_object* v_vals_4270_, lean_object* v_heq_4271_, lean_object* v_i_4272_, lean_object* v_entries_4273_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4268_, v_keys_4269_, v_vals_4270_, v_i_4272_, v_entries_4273_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4275_, lean_object* v_depth_4276_, lean_object* v_keys_4277_, lean_object* v_vals_4278_, lean_object* v_heq_4279_, lean_object* v_i_4280_, lean_object* v_entries_4281_){
_start:
{
size_t v_depth_boxed_4282_; lean_object* v_res_4283_; 
v_depth_boxed_4282_ = lean_unbox_usize(v_depth_4276_);
lean_dec(v_depth_4276_);
v_res_4283_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4275_, v_depth_boxed_4282_, v_keys_4277_, v_vals_4278_, v_heq_4279_, v_i_4280_, v_entries_4281_);
lean_dec_ref(v_vals_4278_);
lean_dec_ref(v_keys_4277_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4284_, lean_object* v_x_4285_, lean_object* v_x_4286_, lean_object* v_x_4287_, lean_object* v_x_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4285_, v_x_4286_, v_x_4287_, v_x_4288_);
return v___x_4289_;
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
