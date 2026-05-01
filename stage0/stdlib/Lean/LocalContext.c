// Lean compiler output
// Module: Lean.LocalContext
// Imports: public import Init.Data.Nat.Control public import Lean.Data.PersistentArray public import Lean.Expr import Init.Data.ToString.Macro import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqFVarId_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashableFVarId_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_sanitizeName(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_foldRev___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getSanitizeNames(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedLocalDeclKind_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedLocalDeclKind;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.LocalDeclKind.default"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__0 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__1 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__1_value;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.LocalDeclKind.implDetail"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__2 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__2_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__3 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__3_value;
static const lean_string_object l_Lean_instReprLocalDeclKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.LocalDeclKind.auxDecl"};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__4 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprLocalDeclKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprLocalDeclKind_repr___closed__5 = (const lean_object*)&l_Lean_instReprLocalDeclKind_repr___closed__5_value;
static lean_once_cell_t l_Lean_instReprLocalDeclKind_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLocalDeclKind_repr___closed__6;
static lean_once_cell_t l_Lean_instReprLocalDeclKind_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprLocalDeclKind_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprLocalDeclKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprLocalDeclKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprLocalDeclKind___closed__0 = (const lean_object*)&l_Lean_instReprLocalDeclKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprLocalDeclKind = (const lean_object*)&l_Lean_instReprLocalDeclKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashableLocalDeclKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableLocalDeclKind_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashableLocalDeclKind___closed__0 = (const lean_object*)&l_Lean_instHashableLocalDeclKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instHashableLocalDeclKind = (const lean_object*)&l_Lean_instHashableLocalDeclKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedLocalDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_instInhabitedLocalDecl_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedLocalDecl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_instInhabitedLocalDecl_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedLocalDecl_default___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedLocalDecl_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalDecl_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedLocalDecl_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalDecl_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalDecl_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalDecl;
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object*);
static const lean_string_object l_Lean_LocalDecl_value___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.LocalContext"};
static const lean_object* l_Lean_LocalDecl_value___closed__0 = (const lean_object*)&l_Lean_LocalDecl_value___closed__0_value;
static const lean_string_object l_Lean_LocalDecl_value___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.LocalDecl.value"};
static const lean_object* l_Lean_LocalDecl_value___closed__1 = (const lean_object*)&l_Lean_LocalDecl_value___closed__1_value;
static const lean_string_object l_Lean_LocalDecl_value___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "let declaration expected"};
static const lean_object* l_Lean_LocalDecl_value___closed__2 = (const lean_object*)&l_Lean_LocalDecl_value___closed__2_value;
static lean_once_cell_t l_Lean_LocalDecl_value___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_value___closed__3;
static const lean_string_object l_Lean_LocalDecl_value___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "dependent let declaration expected"};
static const lean_object* l_Lean_LocalDecl_value___closed__4 = (const lean_object*)&l_Lean_LocalDecl_value___closed__4_value;
static lean_once_cell_t l_Lean_LocalDecl_value___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_value___closed__5;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object*);
static const lean_string_object l_Lean_LocalDecl_setBinderInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.LocalDecl.setBinderInfo"};
static const lean_object* l_Lean_LocalDecl_setBinderInfo___closed__0 = (const lean_object*)&l_Lean_LocalDecl_setBinderInfo___closed__0_value;
static const lean_string_object l_Lean_LocalDecl_setBinderInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected let declaration"};
static const lean_object* l_Lean_LocalDecl_setBinderInfo___closed__1 = (const lean_object*)&l_Lean_LocalDecl_setBinderInfo___closed__1_value;
static lean_once_cell_t l_Lean_LocalDecl_setBinderInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_setBinderInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__3;
static lean_once_cell_t l_Lean_instInhabitedLocalContext_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedLocalContext_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalContext_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedLocalContext;
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_get_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.LocalContext.get!"};
static const lean_object* l_Lean_LocalContext_get_x21___closed__0 = (const lean_object*)&l_Lean_LocalContext_get_x21___closed__0_value;
static const lean_string_object l_Lean_LocalContext_get_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown free variable"};
static const lean_object* l_Lean_LocalContext_get_x21___closed__1 = (const lean_object*)&l_Lean_LocalContext_get_x21___closed__1_value;
static lean_once_cell_t l_Lean_LocalContext_get_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_get_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_LocalContext_getFVarIds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LocalContext_getFVarIds___closed__0 = (const lean_object*)&l_Lean_LocalContext_getFVarIds___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.LocalContext.getFromUserName!"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__0 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__0_value;
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unknown local declaration `"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__1 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__1_value;
static const lean_string_object l_Lean_LocalContext_getFromUserName_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_LocalContext_getFromUserName_x21___closed__2 = (const lean_object*)&l_Lean_LocalContext_getFromUserName_x21___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LocalContext_modifyLocalDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_modifyLocalDecl___closed__0 = (const lean_object*)&l_Lean_LocalContext_modifyLocalDecl___closed__0_value;
static const lean_closure_object l_Lean_LocalContext_modifyLocalDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_modifyLocalDecl___closed__1 = (const lean_object*)&l_Lean_LocalContext_modifyLocalDecl___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__0 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__0_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__1 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__1_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__2 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__2_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__3 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__3_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__4 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__4_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__5 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__5_value;
static const lean_closure_object l_Lean_LocalContext_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__6 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__6_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__0_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__1_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__7 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__7_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__7_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__2_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__3_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__4_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__5_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__8 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__8_value;
static const lean_ctor_object l_Lean_LocalContext_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__8_value),((lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__6_value)}};
static const lean_object* l_Lean_LocalContext_foldl___redArg___closed__9 = (const lean_object*)&l_Lean_LocalContext_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalContext_mkBinding___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.LocalContext.mkBinding"};
static const lean_object* l_Lean_LocalContext_mkBinding___lam__0___closed__0 = (const lean_object*)&l_Lean_LocalContext_mkBinding___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_LocalContext_mkBinding___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalContext_mkBinding___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_LocalContext_findFromUserNames___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LocalContext_findFromUserNames___redArg___closed__0 = (const lean_object*)&l_Lean_LocalContext_findFromUserNames___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getLocalHyps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getLocalHyps___redArg___closed__0 = (const lean_object*)&l_Lean_getLocalHyps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_LocalDeclKind_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_LocalDeclKind_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_LocalDeclKind_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_LocalDeclKind_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_LocalDeclKind_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object* v_default_28_){
_start:
{
lean_inc(v_default_28_);
return v_default_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object* v_default_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_LocalDeclKind_default_elim___redArg(v_default_29_);
lean_dec(v_default_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_default_34_){
_start:
{
lean_inc(v_default_34_);
return v_default_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_default_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_LocalDeclKind_default_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_default_38_);
lean_dec(v_default_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object* v_implDetail_41_){
_start:
{
lean_inc(v_implDetail_41_);
return v_implDetail_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object* v_implDetail_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_LocalDeclKind_implDetail_elim___redArg(v_implDetail_42_);
lean_dec(v_implDetail_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_implDetail_47_){
_start:
{
lean_inc(v_implDetail_47_);
return v_implDetail_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_implDetail_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_LocalDeclKind_implDetail_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_implDetail_51_);
lean_dec(v_implDetail_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object* v_auxDecl_54_){
_start:
{
lean_inc(v_auxDecl_54_);
return v_auxDecl_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object* v_auxDecl_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_LocalDeclKind_auxDecl_elim___redArg(v_auxDecl_55_);
lean_dec(v_auxDecl_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_auxDecl_60_){
_start:
{
lean_inc(v_auxDecl_60_);
return v_auxDecl_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_auxDecl_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_LocalDeclKind_auxDecl_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_auxDecl_64_);
lean_dec(v_auxDecl_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__6(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(2u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__7(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t v_x_82_, lean_object* v_prec_83_){
_start:
{
lean_object* v___y_85_; lean_object* v___y_92_; lean_object* v___y_99_; 
switch(v_x_82_)
{
case 0:
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = lean_nat_dec_le(v___x_105_, v_prec_83_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_85_ = v___x_107_;
goto v___jp_84_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_85_ = v___x_108_;
goto v___jp_84_;
}
}
case 1:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(1024u);
v___x_110_ = lean_nat_dec_le(v___x_109_, v_prec_83_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_92_ = v___x_111_;
goto v___jp_91_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_92_ = v___x_112_;
goto v___jp_91_;
}
}
default: 
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1024u);
v___x_114_ = lean_nat_dec_le(v___x_113_, v_prec_83_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_99_ = v___x_115_;
goto v___jp_98_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_99_ = v___x_116_;
goto v___jp_98_;
}
}
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__1));
lean_inc(v___y_85_);
v___x_87_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_87_, 0, v___y_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = l_Repr_addAppParen(v___x_89_, v_prec_83_);
return v___x_90_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__3));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_83_);
return v___x_97_;
}
v___jp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_100_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__5));
lean_inc(v___y_99_);
v___x_101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_101_, 0, v___y_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = 0;
v___x_103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_102_);
v___x_104_ = l_Repr_addAppParen(v___x_103_, v_prec_83_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object* v_x_117_, lean_object* v_prec_118_){
_start:
{
uint8_t v_x_177__boxed_119_; lean_object* v_res_120_; 
v_x_177__boxed_119_ = lean_unbox(v_x_117_);
v_res_120_ = l_Lean_instReprLocalDeclKind_repr(v_x_177__boxed_119_, v_prec_118_);
lean_dec(v_prec_118_);
return v_res_120_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object* v_n_123_){
_start:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_nat_dec_le(v_n_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_dec_le(v_n_123_, v___x_126_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = 2;
return v___x_128_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 1;
return v___x_129_;
}
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object* v_n_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_LocalDeclKind_ofNat(v_n_131_);
lean_dec(v_n_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t v_x_134_, uint8_t v_y_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = l_Lean_LocalDeclKind_ctorIdx(v_x_134_);
v___x_137_ = l_Lean_LocalDeclKind_ctorIdx(v_y_135_);
v___x_138_ = lean_nat_dec_eq(v___x_136_, v___x_137_);
lean_dec(v___x_137_);
lean_dec(v___x_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object* v_x_139_, lean_object* v_y_140_){
_start:
{
uint8_t v_x_13__boxed_141_; uint8_t v_y_14__boxed_142_; uint8_t v_res_143_; lean_object* v_r_144_; 
v_x_13__boxed_141_ = lean_unbox(v_x_139_);
v_y_14__boxed_142_ = lean_unbox(v_y_140_);
v_res_143_ = l_Lean_instDecidableEqLocalDeclKind(v_x_13__boxed_141_, v_y_14__boxed_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t v_x_145_){
_start:
{
switch(v_x_145_)
{
case 0:
{
uint64_t v___x_146_; 
v___x_146_ = 0ULL;
return v___x_146_;
}
case 1:
{
uint64_t v___x_147_; 
v___x_147_ = 1ULL;
return v___x_147_;
}
default: 
{
uint64_t v___x_148_; 
v___x_148_ = 2ULL;
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object* v_x_149_){
_start:
{
uint8_t v_x_40__boxed_150_; uint64_t v_res_151_; lean_object* v_r_152_; 
v_x_40__boxed_150_ = lean_unbox(v_x_149_);
v_res_151_ = l_Lean_instHashableLocalDeclKind_hash(v_x_40__boxed_150_);
v_r_152_ = lean_box_uint64(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object* v_x_155_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_unsigned_to_nat(0u);
return v___x_156_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_unsigned_to_nat(1u);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object* v_x_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_LocalDecl_ctorIdx(v_x_158_);
lean_dec_ref(v_x_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object* v_t_160_, lean_object* v_k_161_){
_start:
{
if (lean_obj_tag(v_t_160_) == 0)
{
lean_object* v_index_162_; lean_object* v_fvarId_163_; lean_object* v_userName_164_; lean_object* v_type_165_; uint8_t v_bi_166_; uint8_t v_kind_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_index_162_ = lean_ctor_get(v_t_160_, 0);
lean_inc(v_index_162_);
v_fvarId_163_ = lean_ctor_get(v_t_160_, 1);
lean_inc(v_fvarId_163_);
v_userName_164_ = lean_ctor_get(v_t_160_, 2);
lean_inc(v_userName_164_);
v_type_165_ = lean_ctor_get(v_t_160_, 3);
lean_inc_ref(v_type_165_);
v_bi_166_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*4);
v_kind_167_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*4 + 1);
lean_dec_ref(v_t_160_);
v___x_168_ = lean_box(v_bi_166_);
v___x_169_ = lean_box(v_kind_167_);
v___x_170_ = lean_apply_6(v_k_161_, v_index_162_, v_fvarId_163_, v_userName_164_, v_type_165_, v___x_168_, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v_index_171_; lean_object* v_fvarId_172_; lean_object* v_userName_173_; lean_object* v_type_174_; lean_object* v_value_175_; uint8_t v_nondep_176_; uint8_t v_kind_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_index_171_ = lean_ctor_get(v_t_160_, 0);
lean_inc(v_index_171_);
v_fvarId_172_ = lean_ctor_get(v_t_160_, 1);
lean_inc(v_fvarId_172_);
v_userName_173_ = lean_ctor_get(v_t_160_, 2);
lean_inc(v_userName_173_);
v_type_174_ = lean_ctor_get(v_t_160_, 3);
lean_inc_ref(v_type_174_);
v_value_175_ = lean_ctor_get(v_t_160_, 4);
lean_inc_ref(v_value_175_);
v_nondep_176_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*5);
v_kind_177_ = lean_ctor_get_uint8(v_t_160_, sizeof(void*)*5 + 1);
lean_dec_ref(v_t_160_);
v___x_178_ = lean_box(v_nondep_176_);
v___x_179_ = lean_box(v_kind_177_);
v___x_180_ = lean_apply_7(v_k_161_, v_index_171_, v_fvarId_172_, v_userName_173_, v_type_174_, v_value_175_, v___x_178_, v___x_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object* v_motive_181_, lean_object* v_ctorIdx_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_k_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_183_, v_k_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_LocalDecl_ctorElim(v_motive_187_, v_ctorIdx_188_, v_t_189_, v_h_190_, v_k_191_);
lean_dec(v_ctorIdx_188_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object* v_t_193_, lean_object* v_cdecl_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_193_, v_cdecl_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_cdecl_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_197_, v_cdecl_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object* v_t_201_, lean_object* v_ldecl_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_201_, v_ldecl_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_ldecl_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_205_, v_ldecl_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__2(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_box(0);
v___x_213_ = ((lean_object*)(l_Lean_instInhabitedLocalDecl_default___closed__1));
v___x_214_ = l_Lean_Expr_const___override(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__3(void){
_start:
{
uint8_t v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_215_ = 0;
v___x_216_ = 0;
v___x_217_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__2, &l_Lean_instInhabitedLocalDecl_default___closed__2_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__2);
v___x_218_ = lean_box(0);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___x_218_);
lean_ctor_set(v___x_220_, 3, v___x_217_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*4, v___x_216_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*4 + 1, v___x_215_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default(void){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__3, &l_Lean_instInhabitedLocalDecl_default___closed__3_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__3);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_instInhabitedLocalDecl_default;
return v___x_222_;
}
}
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object* v_index_223_, lean_object* v_fvarId_224_, lean_object* v_userName_225_, lean_object* v_type_226_, uint8_t v_bi_227_){
_start:
{
uint8_t v___x_228_; lean_object* v___x_229_; 
v___x_228_ = 0;
v___x_229_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_229_, 0, v_index_223_);
lean_ctor_set(v___x_229_, 1, v_fvarId_224_);
lean_ctor_set(v___x_229_, 2, v_userName_225_);
lean_ctor_set(v___x_229_, 3, v_type_226_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*4, v_bi_227_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*4 + 1, v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* v_index_230_, lean_object* v_fvarId_231_, lean_object* v_userName_232_, lean_object* v_type_233_, lean_object* v_bi_234_){
_start:
{
uint8_t v_bi_boxed_235_; lean_object* v_res_236_; 
v_bi_boxed_235_ = lean_unbox(v_bi_234_);
v_res_236_ = lean_mk_local_decl(v_index_230_, v_fvarId_231_, v_userName_232_, v_type_233_, v_bi_boxed_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* v_index_237_, lean_object* v_fvarId_238_, lean_object* v_userName_239_, lean_object* v_type_240_, lean_object* v_val_241_){
_start:
{
uint8_t v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; 
v___x_242_ = 0;
v___x_243_ = 0;
v___x_244_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_244_, 0, v_index_237_);
lean_ctor_set(v___x_244_, 1, v_fvarId_238_);
lean_ctor_set(v___x_244_, 2, v_userName_239_);
lean_ctor_set(v___x_244_, 3, v_type_240_);
lean_ctor_set(v___x_244_, 4, v_val_241_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*5, v___x_242_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*5 + 1, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
uint8_t v_bi_246_; 
v_bi_246_ = lean_ctor_get_uint8(v_x_245_, sizeof(void*)*4);
lean_dec_ref(v_x_245_);
return v_bi_246_;
}
else
{
uint8_t v___x_247_; 
lean_dec_ref(v_x_245_);
v___x_247_ = 0;
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* v_x_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = lean_local_decl_binder_info(v_x_248_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object* v_x_251_, uint8_t v_x_252_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
uint8_t v___x_253_; 
v___x_253_ = 0;
return v___x_253_;
}
else
{
uint8_t v_nondep_254_; 
v_nondep_254_ = lean_ctor_get_uint8(v_x_251_, sizeof(void*)*5);
if (v_nondep_254_ == 0)
{
uint8_t v___x_255_; 
v___x_255_ = 1;
return v___x_255_;
}
else
{
return v_x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_x_53__boxed_258_; uint8_t v_res_259_; lean_object* v_r_260_; 
v_x_53__boxed_258_ = lean_unbox(v_x_257_);
v_res_259_ = l_Lean_LocalDecl_isLet(v_x_256_, v_x_53__boxed_258_);
lean_dec_ref(v_x_256_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* v_x_261_){
_start:
{
lean_object* v_index_262_; 
v_index_262_ = lean_ctor_get(v_x_261_, 0);
lean_inc(v_index_262_);
return v_index_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_LocalDecl_index(v_x_263_);
lean_dec_ref(v_x_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
lean_object* v_fvarId_267_; lean_object* v_userName_268_; lean_object* v_type_269_; uint8_t v_bi_270_; uint8_t v_kind_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_fvarId_267_ = lean_ctor_get(v_x_265_, 1);
v_userName_268_ = lean_ctor_get(v_x_265_, 2);
v_type_269_ = lean_ctor_get(v_x_265_, 3);
v_bi_270_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*4);
v_kind_271_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*4 + 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_265_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v_x_265_, 0);
lean_dec(v_unused_279_);
v___x_273_ = v_x_265_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_type_269_);
lean_inc(v_userName_268_);
lean_inc(v_fvarId_267_);
lean_dec(v_x_265_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v_x_266_);
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_x_266_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_fvarId_267_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v_userName_268_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_type_269_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*4, v_bi_270_);
lean_ctor_set_uint8(v_reuseFailAlloc_277_, sizeof(void*)*4 + 1, v_kind_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_object* v_fvarId_280_; lean_object* v_userName_281_; lean_object* v_type_282_; lean_object* v_value_283_; uint8_t v_nondep_284_; uint8_t v_kind_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_fvarId_280_ = lean_ctor_get(v_x_265_, 1);
v_userName_281_ = lean_ctor_get(v_x_265_, 2);
v_type_282_ = lean_ctor_get(v_x_265_, 3);
v_value_283_ = lean_ctor_get(v_x_265_, 4);
v_nondep_284_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*5);
v_kind_285_ = lean_ctor_get_uint8(v_x_265_, sizeof(void*)*5 + 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_265_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v_x_265_, 0);
lean_dec(v_unused_293_);
v___x_287_ = v_x_265_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_value_283_);
lean_inc(v_type_282_);
lean_inc(v_userName_281_);
lean_inc(v_fvarId_280_);
lean_dec(v_x_265_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v_x_266_);
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_x_266_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_fvarId_280_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_userName_281_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_type_282_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_value_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*5, v_nondep_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_291_, sizeof(void*)*5 + 1, v_kind_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* v_x_294_){
_start:
{
lean_object* v_fvarId_295_; 
v_fvarId_295_ = lean_ctor_get(v_x_294_, 1);
lean_inc(v_fvarId_295_);
return v_fvarId_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_LocalDecl_fvarId(v_x_296_);
lean_dec_ref(v_x_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* v_x_298_){
_start:
{
lean_object* v_userName_299_; 
v_userName_299_ = lean_ctor_get(v_x_298_, 2);
lean_inc(v_userName_299_);
return v_userName_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* v_x_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_LocalDecl_userName(v_x_300_);
lean_dec_ref(v_x_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* v_x_302_){
_start:
{
lean_object* v_type_303_; 
v_type_303_ = lean_ctor_get(v_x_302_, 3);
lean_inc_ref(v_type_303_);
return v_type_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* v_x_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_LocalDecl_type(v_x_304_);
lean_dec_ref(v_x_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_306_) == 0)
{
lean_object* v_index_308_; lean_object* v_fvarId_309_; lean_object* v_userName_310_; uint8_t v_bi_311_; uint8_t v_kind_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_index_308_ = lean_ctor_get(v_x_306_, 0);
v_fvarId_309_ = lean_ctor_get(v_x_306_, 1);
v_userName_310_ = lean_ctor_get(v_x_306_, 2);
v_bi_311_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*4);
v_kind_312_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*4 + 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v_x_306_, 3);
lean_dec(v_unused_320_);
v___x_314_ = v_x_306_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_userName_310_);
lean_inc(v_fvarId_309_);
lean_inc(v_index_308_);
lean_dec(v_x_306_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 3, v_x_307_);
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_index_308_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_fvarId_309_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_userName_310_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_x_307_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*4, v_bi_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*4 + 1, v_kind_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_index_321_; lean_object* v_fvarId_322_; lean_object* v_userName_323_; lean_object* v_value_324_; uint8_t v_nondep_325_; uint8_t v_kind_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
v_index_321_ = lean_ctor_get(v_x_306_, 0);
v_fvarId_322_ = lean_ctor_get(v_x_306_, 1);
v_userName_323_ = lean_ctor_get(v_x_306_, 2);
v_value_324_ = lean_ctor_get(v_x_306_, 4);
v_nondep_325_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*5);
v_kind_326_ = lean_ctor_get_uint8(v_x_306_, sizeof(void*)*5 + 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_x_306_, 3);
lean_dec(v_unused_334_);
v___x_328_ = v_x_306_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_value_324_);
lean_inc(v_userName_323_);
lean_inc(v_fvarId_322_);
lean_inc(v_index_321_);
lean_dec(v_x_306_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 3, v_x_307_);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_index_321_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_fvarId_322_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_userName_323_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v_x_307_);
lean_ctor_set(v_reuseFailAlloc_332_, 4, v_value_324_);
lean_ctor_set_uint8(v_reuseFailAlloc_332_, sizeof(void*)*5, v_nondep_325_);
lean_ctor_set_uint8(v_reuseFailAlloc_332_, sizeof(void*)*5 + 1, v_kind_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object* v_x_335_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
uint8_t v_bi_336_; 
v_bi_336_ = lean_ctor_get_uint8(v_x_335_, sizeof(void*)*4);
return v_bi_336_;
}
else
{
uint8_t v___x_337_; 
v___x_337_ = 0;
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* v_x_338_){
_start:
{
uint8_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Lean_LocalDecl_binderInfo(v_x_338_);
lean_dec_ref(v_x_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object* v_x_341_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
uint8_t v_kind_342_; 
v_kind_342_ = lean_ctor_get_uint8(v_x_341_, sizeof(void*)*4 + 1);
return v_kind_342_;
}
else
{
uint8_t v_kind_343_; 
v_kind_343_ = lean_ctor_get_uint8(v_x_341_, sizeof(void*)*5 + 1);
return v_kind_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* v_x_344_){
_start:
{
uint8_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = l_Lean_LocalDecl_kind(v_x_344_);
lean_dec_ref(v_x_344_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* v_d_347_){
_start:
{
uint8_t v___y_349_; 
if (lean_obj_tag(v_d_347_) == 0)
{
uint8_t v_kind_352_; 
v_kind_352_ = lean_ctor_get_uint8(v_d_347_, sizeof(void*)*4 + 1);
v___y_349_ = v_kind_352_;
goto v___jp_348_;
}
else
{
uint8_t v_kind_353_; 
v_kind_353_ = lean_ctor_get_uint8(v_d_347_, sizeof(void*)*5 + 1);
v___y_349_ = v_kind_353_;
goto v___jp_348_;
}
v___jp_348_:
{
uint8_t v___x_350_; uint8_t v___x_351_; 
v___x_350_ = 2;
v___x_351_ = l_Lean_instDecidableEqLocalDeclKind(v___y_349_, v___x_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* v_d_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lean_LocalDecl_isAuxDecl(v_d_354_);
lean_dec_ref(v_d_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* v_d_357_){
_start:
{
uint8_t v___y_359_; 
if (lean_obj_tag(v_d_357_) == 0)
{
uint8_t v_kind_364_; 
v_kind_364_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*4 + 1);
v___y_359_ = v_kind_364_;
goto v___jp_358_;
}
else
{
uint8_t v_kind_365_; 
v_kind_365_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*5 + 1);
v___y_359_ = v_kind_365_;
goto v___jp_358_;
}
v___jp_358_:
{
uint8_t v___x_360_; uint8_t v___x_361_; 
v___x_360_ = 0;
v___x_361_ = l_Lean_instDecidableEqLocalDeclKind(v___y_359_, v___x_360_);
if (v___x_361_ == 0)
{
uint8_t v___x_362_; 
v___x_362_ = 1;
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* v_d_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Lean_LocalDecl_isImplementationDetail(v_d_366_);
lean_dec_ref(v_d_366_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object* v_x_369_, uint8_t v_x_370_){
_start:
{
if (lean_obj_tag(v_x_369_) == 1)
{
uint8_t v_nondep_371_; 
v_nondep_371_ = lean_ctor_get_uint8(v_x_369_, sizeof(void*)*5);
if (v_nondep_371_ == 0)
{
lean_object* v_value_372_; lean_object* v___x_373_; 
v_value_372_ = lean_ctor_get(v_x_369_, 4);
lean_inc_ref(v_value_372_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v_value_372_);
return v___x_373_;
}
else
{
if (v_x_370_ == 1)
{
lean_object* v_value_374_; lean_object* v___x_375_; 
v_value_374_ = lean_ctor_get(v_x_369_, 4);
lean_inc_ref(v_value_374_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v_value_374_);
return v___x_375_;
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
}
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
uint8_t v_x_57__boxed_380_; lean_object* v_res_381_; 
v_x_57__boxed_380_ = lean_unbox(v_x_379_);
v_res_381_ = l_Lean_LocalDecl_value_x3f(v_x_378_, v_x_57__boxed_380_);
lean_dec_ref(v_x_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = l_Lean_instInhabitedExpr;
v___x_384_ = lean_panic_fn_borrowed(v___x_383_, v_msg_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_388_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__2));
v___x_389_ = lean_unsigned_to_nat(54u);
v___x_390_ = lean_unsigned_to_nat(172u);
v___x_391_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_392_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_393_ = l_mkPanicMessageWithDecl(v___x_392_, v___x_391_, v___x_390_, v___x_389_, v___x_388_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__5(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_395_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__4));
v___x_396_ = lean_unsigned_to_nat(54u);
v___x_397_ = lean_unsigned_to_nat(175u);
v___x_398_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_399_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_400_ = l_mkPanicMessageWithDecl(v___x_399_, v___x_398_, v___x_397_, v___x_396_, v___x_395_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object* v_x_401_, uint8_t v_x_402_){
_start:
{
if (lean_obj_tag(v_x_401_) == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__3, &l_Lean_LocalDecl_value___closed__3_once, _init_l_Lean_LocalDecl_value___closed__3);
v___x_404_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_403_);
return v___x_404_;
}
else
{
uint8_t v_nondep_405_; 
v_nondep_405_ = lean_ctor_get_uint8(v_x_401_, sizeof(void*)*5);
if (v_nondep_405_ == 0)
{
lean_object* v_value_406_; 
v_value_406_ = lean_ctor_get(v_x_401_, 4);
lean_inc_ref(v_value_406_);
return v_value_406_;
}
else
{
if (v_x_402_ == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__5, &l_Lean_LocalDecl_value___closed__5_once, _init_l_Lean_LocalDecl_value___closed__5);
v___x_408_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_407_);
return v___x_408_;
}
else
{
lean_object* v_value_409_; 
v_value_409_ = lean_ctor_get(v_x_401_, 4);
lean_inc_ref(v_value_409_);
return v_value_409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
uint8_t v_x_143__boxed_412_; lean_object* v_res_413_; 
v_x_143__boxed_412_ = lean_unbox(v_x_411_);
v_res_413_ = l_Lean_LocalDecl_value(v_x_410_, v_x_143__boxed_412_);
lean_dec_ref(v_x_410_);
return v_res_413_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object* v_x_414_, uint8_t v_x_415_){
_start:
{
if (lean_obj_tag(v_x_414_) == 0)
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
else
{
uint8_t v_nondep_417_; 
v_nondep_417_ = lean_ctor_get_uint8(v_x_414_, sizeof(void*)*5);
if (v_nondep_417_ == 0)
{
uint8_t v___x_418_; 
v___x_418_ = 1;
return v___x_418_;
}
else
{
return v_x_415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
uint8_t v_x_72__boxed_421_; uint8_t v_res_422_; lean_object* v_r_423_; 
v_x_72__boxed_421_ = lean_unbox(v_x_420_);
v_res_422_ = l_Lean_LocalDecl_hasValue(v_x_419_, v_x_72__boxed_421_);
lean_dec_ref(v_x_419_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
if (lean_obj_tag(v_x_424_) == 1)
{
lean_object* v_index_426_; lean_object* v_fvarId_427_; lean_object* v_userName_428_; lean_object* v_type_429_; uint8_t v_nondep_430_; uint8_t v_kind_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_index_426_ = lean_ctor_get(v_x_424_, 0);
v_fvarId_427_ = lean_ctor_get(v_x_424_, 1);
v_userName_428_ = lean_ctor_get(v_x_424_, 2);
v_type_429_ = lean_ctor_get(v_x_424_, 3);
v_nondep_430_ = lean_ctor_get_uint8(v_x_424_, sizeof(void*)*5);
v_kind_431_ = lean_ctor_get_uint8(v_x_424_, sizeof(void*)*5 + 1);
v_isSharedCheck_438_ = !lean_is_exclusive(v_x_424_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v_x_424_, 4);
lean_dec(v_unused_439_);
v___x_433_ = v_x_424_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_type_429_);
lean_inc(v_userName_428_);
lean_inc(v_fvarId_427_);
lean_inc(v_index_426_);
lean_dec(v_x_424_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 4, v_x_425_);
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_index_426_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_fvarId_427_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_userName_428_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_type_429_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_x_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*5, v_nondep_430_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*5 + 1, v_kind_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_dec_ref(v_x_425_);
return v_x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object* v_x_440_, uint8_t v_x_441_){
_start:
{
if (lean_obj_tag(v_x_440_) == 1)
{
lean_object* v_index_442_; lean_object* v_fvarId_443_; lean_object* v_userName_444_; lean_object* v_type_445_; lean_object* v_value_446_; uint8_t v_kind_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
v_index_442_ = lean_ctor_get(v_x_440_, 0);
v_fvarId_443_ = lean_ctor_get(v_x_440_, 1);
v_userName_444_ = lean_ctor_get(v_x_440_, 2);
v_type_445_ = lean_ctor_get(v_x_440_, 3);
v_value_446_ = lean_ctor_get(v_x_440_, 4);
v_kind_447_ = lean_ctor_get_uint8(v_x_440_, sizeof(void*)*5 + 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v_x_440_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_value_446_);
lean_inc(v_type_445_);
lean_inc(v_userName_444_);
lean_inc(v_fvarId_443_);
lean_inc(v_index_442_);
lean_dec(v_x_440_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_index_442_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_fvarId_443_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_userName_444_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_type_445_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_value_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_453_, sizeof(void*)*5 + 1, v_kind_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_ctor_set_uint8(v___x_452_, sizeof(void*)*5, v_x_441_);
return v___x_452_;
}
}
}
else
{
return v_x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
uint8_t v_x_27__boxed_457_; lean_object* v_res_458_; 
v_x_27__boxed_457_ = lean_unbox(v_x_456_);
v_res_458_ = l_Lean_LocalDecl_setNondep(v_x_455_, v_x_27__boxed_457_);
return v_res_458_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 1)
{
uint8_t v_nondep_460_; 
v_nondep_460_ = lean_ctor_get_uint8(v_x_459_, sizeof(void*)*5);
return v_nondep_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object* v_x_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Lean_LocalDecl_isNondep(v_x_462_);
lean_dec_ref(v_x_462_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_object* v_index_467_; lean_object* v_fvarId_468_; lean_object* v_type_469_; uint8_t v_bi_470_; uint8_t v_kind_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
v_index_467_ = lean_ctor_get(v_x_465_, 0);
v_fvarId_468_ = lean_ctor_get(v_x_465_, 1);
v_type_469_ = lean_ctor_get(v_x_465_, 3);
v_bi_470_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*4);
v_kind_471_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*4 + 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_x_465_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v_x_465_, 2);
lean_dec(v_unused_479_);
v___x_473_ = v_x_465_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_type_469_);
lean_inc(v_fvarId_468_);
lean_inc(v_index_467_);
lean_dec(v_x_465_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 2, v_x_466_);
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_index_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_fvarId_468_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_x_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_type_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*4, v_bi_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*4 + 1, v_kind_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
lean_object* v_index_480_; lean_object* v_fvarId_481_; lean_object* v_type_482_; lean_object* v_value_483_; uint8_t v_nondep_484_; uint8_t v_kind_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
v_index_480_ = lean_ctor_get(v_x_465_, 0);
v_fvarId_481_ = lean_ctor_get(v_x_465_, 1);
v_type_482_ = lean_ctor_get(v_x_465_, 3);
v_value_483_ = lean_ctor_get(v_x_465_, 4);
v_nondep_484_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*5);
v_kind_485_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*5 + 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_465_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v_x_465_, 2);
lean_dec(v_unused_493_);
v___x_487_ = v_x_465_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_value_483_);
lean_inc(v_type_482_);
lean_inc(v_fvarId_481_);
lean_inc(v_index_480_);
lean_dec(v_x_465_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 2, v_x_466_);
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_index_480_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_fvarId_481_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_x_466_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_type_482_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_value_483_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*5, v_nondep_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*5 + 1, v_kind_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object* v_msg_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = l_Lean_instInhabitedLocalDecl_default;
v___x_496_ = lean_panic_fn_borrowed(v___x_495_, v_msg_494_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_499_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__1));
v___x_500_ = lean_unsigned_to_nat(38u);
v___x_501_ = lean_unsigned_to_nat(237u);
v___x_502_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__0));
v___x_503_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_504_ = l_mkPanicMessageWithDecl(v___x_503_, v___x_502_, v___x_501_, v___x_500_, v___x_499_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* v_x_505_, uint8_t v_x_506_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
lean_object* v_index_507_; lean_object* v_fvarId_508_; lean_object* v_userName_509_; lean_object* v_type_510_; uint8_t v_kind_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_index_507_ = lean_ctor_get(v_x_505_, 0);
v_fvarId_508_ = lean_ctor_get(v_x_505_, 1);
v_userName_509_ = lean_ctor_get(v_x_505_, 2);
v_type_510_ = lean_ctor_get(v_x_505_, 3);
v_kind_511_ = lean_ctor_get_uint8(v_x_505_, sizeof(void*)*4 + 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_x_505_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v_x_505_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_type_510_);
lean_inc(v_userName_509_);
lean_inc(v_fvarId_508_);
lean_inc(v_index_507_);
lean_dec(v_x_505_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_index_507_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_fvarId_508_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_userName_509_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_type_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_517_, sizeof(void*)*4 + 1, v_kind_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_ctor_set_uint8(v___x_516_, sizeof(void*)*4, v_x_506_);
return v___x_516_;
}
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec_ref(v_x_505_);
v___x_519_ = lean_obj_once(&l_Lean_LocalDecl_setBinderInfo___closed__2, &l_Lean_LocalDecl_setBinderInfo___closed__2_once, _init_l_Lean_LocalDecl_setBinderInfo___closed__2);
v___x_520_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_519_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
uint8_t v_x_84__boxed_523_; lean_object* v_res_524_; 
v_x_84__boxed_523_ = lean_unbox(v_x_522_);
v_res_524_ = l_Lean_LocalDecl_setBinderInfo(v_x_521_, v_x_84__boxed_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* v_decl_525_){
_start:
{
lean_object* v_fvarId_526_; lean_object* v___x_527_; 
v_fvarId_526_ = lean_ctor_get(v_decl_525_, 1);
lean_inc(v_fvarId_526_);
lean_dec_ref(v_decl_525_);
v___x_527_ = l_Lean_mkFVar(v_fvarId_526_);
return v___x_527_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* v_x_528_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v_type_529_; uint8_t v___x_530_; 
v_type_529_ = lean_ctor_get(v_x_528_, 3);
v___x_530_ = l_Lean_Expr_hasExprMVar(v_type_529_);
return v___x_530_;
}
else
{
lean_object* v_type_531_; lean_object* v_value_532_; uint8_t v___x_533_; 
v_type_531_ = lean_ctor_get(v_x_528_, 3);
v_value_532_ = lean_ctor_get(v_x_528_, 4);
v___x_533_ = l_Lean_Expr_hasExprMVar(v_type_531_);
if (v___x_533_ == 0)
{
uint8_t v___x_534_; 
v___x_534_ = l_Lean_Expr_hasExprMVar(v_value_532_);
return v___x_534_;
}
else
{
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* v_x_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Lean_LocalDecl_hasExprMVar(v_x_535_);
lean_dec_ref(v_x_535_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object* v_x_538_, uint8_t v_x_539_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_object* v_index_540_; lean_object* v_fvarId_541_; lean_object* v_userName_542_; lean_object* v_type_543_; uint8_t v_bi_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_index_540_ = lean_ctor_get(v_x_538_, 0);
v_fvarId_541_ = lean_ctor_get(v_x_538_, 1);
v_userName_542_ = lean_ctor_get(v_x_538_, 2);
v_type_543_ = lean_ctor_get(v_x_538_, 3);
v_bi_544_ = lean_ctor_get_uint8(v_x_538_, sizeof(void*)*4);
v_isSharedCheck_551_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v_x_538_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_type_543_);
lean_inc(v_userName_542_);
lean_inc(v_fvarId_541_);
lean_inc(v_index_540_);
lean_dec(v_x_538_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_index_540_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_fvarId_541_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_userName_542_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_type_543_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*4, v_bi_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*4 + 1, v_x_539_);
return v___x_549_;
}
}
}
else
{
lean_object* v_index_552_; lean_object* v_fvarId_553_; lean_object* v_userName_554_; lean_object* v_type_555_; lean_object* v_value_556_; uint8_t v_nondep_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
v_index_552_ = lean_ctor_get(v_x_538_, 0);
v_fvarId_553_ = lean_ctor_get(v_x_538_, 1);
v_userName_554_ = lean_ctor_get(v_x_538_, 2);
v_type_555_ = lean_ctor_get(v_x_538_, 3);
v_value_556_ = lean_ctor_get(v_x_538_, 4);
v_nondep_557_ = lean_ctor_get_uint8(v_x_538_, sizeof(void*)*5);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v_x_538_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_value_556_);
lean_inc(v_type_555_);
lean_inc(v_userName_554_);
lean_inc(v_fvarId_553_);
lean_inc(v_index_552_);
lean_dec(v_x_538_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_index_552_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_fvarId_553_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_userName_554_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_type_555_);
lean_ctor_set(v_reuseFailAlloc_563_, 4, v_value_556_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, sizeof(void*)*5, v_nondep_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*5 + 1, v_x_539_);
return v___x_562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
uint8_t v_x_31__boxed_567_; lean_object* v_res_568_; 
v_x_31__boxed_567_ = lean_unbox(v_x_566_);
v_res_568_ = l_Lean_LocalDecl_setKind(v_x_565_, v_x_31__boxed_567_);
return v_res_568_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__0(void){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_569_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__0, &l_Lean_instInhabitedLocalContext_default___closed__0_once, _init_l_Lean_instInhabitedLocalContext_default___closed__0);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__2(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(32u);
v___x_573_ = lean_mk_empty_array_with_capacity(v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
size_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_575_ = ((size_t)5ULL);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_unsigned_to_nat(32u);
v___x_578_ = lean_mk_empty_array_with_capacity(v___x_577_);
v___x_579_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_580_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
lean_ctor_set(v___x_580_, 2, v___x_576_);
lean_ctor_set(v___x_580_, 3, v___x_576_);
lean_ctor_set_usize(v___x_580_, 4, v___x_575_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__4(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = lean_box(1);
v___x_582_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
v___x_583_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___x_582_);
lean_ctor_set(v___x_584_, 2, v___x_581_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_instInhabitedLocalContext_default;
return v___x_586_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(32u);
v___x_589_ = lean_mk_empty_array_with_capacity(v___x_588_);
lean_dec_ref(v___x_589_);
v___x_590_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_unsigned_to_nat(32u);
v___x_592_ = lean_mk_empty_array_with_capacity(v___x_591_);
lean_dec_ref(v___x_592_);
v___x_593_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_593_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_594_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_596_);
lean_dec_ref(v_x_596_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_599_, lean_object* v_x_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_602_, lean_object* v_x_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_602_, v_x_603_);
lean_dec_ref(v_x_603_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object* v_lctx_606_){
_start:
{
lean_object* v_fvarIdToDecl_607_; uint8_t v___x_608_; 
v_fvarIdToDecl_607_ = lean_ctor_get(v_lctx_606_, 0);
lean_inc_ref(v_fvarIdToDecl_607_);
lean_dec_ref(v_lctx_606_);
v___x_608_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_607_);
lean_dec_ref(v_fvarIdToDecl_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = lean_local_ctx_is_empty(v_lctx_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v_ks_616_; lean_object* v_vs_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_641_; 
v_ks_616_ = lean_ctor_get(v_x_612_, 0);
v_vs_617_ = lean_ctor_get(v_x_612_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_612_);
if (v_isSharedCheck_641_ == 0)
{
v___x_619_ = v_x_612_;
v_isShared_620_ = v_isSharedCheck_641_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_vs_617_);
lean_inc(v_ks_616_);
lean_dec(v_x_612_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_641_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_array_get_size(v_ks_616_);
v___x_622_ = lean_nat_dec_lt(v_x_613_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
lean_dec(v_x_613_);
v___x_623_ = lean_array_push(v_ks_616_, v_x_614_);
v___x_624_ = lean_array_push(v_vs_617_, v_x_615_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_624_);
lean_ctor_set(v___x_619_, 0, v___x_623_);
v___x_626_ = v___x_619_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
lean_object* v_k_x27_628_; uint8_t v___x_629_; 
v_k_x27_628_ = lean_array_fget_borrowed(v_ks_616_, v_x_613_);
v___x_629_ = l_Lean_instBEqFVarId_beq(v_x_614_, v_k_x27_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_631_; 
if (v_isShared_620_ == 0)
{
v___x_631_ = v___x_619_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_ks_616_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_vs_617_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_nat_add(v_x_613_, v___x_632_);
lean_dec(v_x_613_);
v_x_612_ = v___x_631_;
v_x_613_ = v___x_633_;
goto _start;
}
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_636_ = lean_array_fset(v_ks_616_, v_x_613_, v_x_614_);
v___x_637_ = lean_array_fset(v_vs_617_, v_x_613_, v_x_615_);
lean_dec(v_x_613_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_637_);
lean_ctor_set(v___x_619_, 0, v___x_636_);
v___x_639_ = v___x_619_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_642_, lean_object* v_k_643_, lean_object* v_v_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_642_, v___x_645_, v_k_643_, v_v_644_);
return v___x_646_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_647_; size_t v___x_648_; size_t v___x_649_; 
v___x_647_ = ((size_t)5ULL);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_shift_left(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_650_; size_t v___x_651_; size_t v___x_652_; 
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_652_ = lean_usize_sub(v___x_651_, v___x_650_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_654_, size_t v_x_655_, size_t v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v_es_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; lean_object* v_j_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_es_659_ = lean_ctor_get(v_x_654_, 0);
v___x_660_ = ((size_t)5ULL);
v___x_661_ = ((size_t)1ULL);
v___x_662_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_663_ = lean_usize_land(v_x_655_, v___x_662_);
v_j_664_ = lean_usize_to_nat(v___x_663_);
v___x_665_ = lean_array_get_size(v_es_659_);
v___x_666_ = lean_nat_dec_lt(v_j_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_dec(v_j_664_);
lean_dec(v_x_658_);
lean_dec(v_x_657_);
return v_x_654_;
}
else
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_703_; 
lean_inc_ref(v_es_659_);
v_isSharedCheck_703_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_x_654_, 0);
lean_dec(v_unused_704_);
v___x_668_ = v_x_654_;
v_isShared_669_ = v_isSharedCheck_703_;
goto v_resetjp_667_;
}
else
{
lean_dec(v_x_654_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_703_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_v_670_; lean_object* v___x_671_; lean_object* v_xs_x27_672_; lean_object* v___y_674_; 
v_v_670_ = lean_array_fget(v_es_659_, v_j_664_);
v___x_671_ = lean_box(0);
v_xs_x27_672_ = lean_array_fset(v_es_659_, v_j_664_, v___x_671_);
switch(lean_obj_tag(v_v_670_))
{
case 0:
{
lean_object* v_key_679_; lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_690_; 
v_key_679_ = lean_ctor_get(v_v_670_, 0);
v_val_680_ = lean_ctor_get(v_v_670_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_v_670_);
if (v_isSharedCheck_690_ == 0)
{
v___x_682_ = v_v_670_;
v_isShared_683_ = v_isSharedCheck_690_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_inc(v_key_679_);
lean_dec(v_v_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_690_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___x_684_; 
v___x_684_ = l_Lean_instBEqFVarId_beq(v_x_657_, v_key_679_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_del_object(v___x_682_);
v___x_685_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_679_, v_val_680_, v_x_657_, v_x_658_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
v___y_674_ = v___x_686_;
goto v___jp_673_;
}
else
{
lean_object* v___x_688_; 
lean_dec(v_val_680_);
lean_dec(v_key_679_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v_x_658_);
lean_ctor_set(v___x_682_, 0, v_x_657_);
v___x_688_ = v___x_682_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_x_657_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_x_658_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
v___y_674_ = v___x_688_;
goto v___jp_673_;
}
}
}
}
case 1:
{
lean_object* v_node_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_701_; 
v_node_691_ = lean_ctor_get(v_v_670_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_v_670_);
if (v_isSharedCheck_701_ == 0)
{
v___x_693_ = v_v_670_;
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_node_691_);
lean_dec(v_v_670_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_701_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_695_ = lean_usize_shift_right(v_x_655_, v___x_660_);
v___x_696_ = lean_usize_add(v_x_656_, v___x_661_);
v___x_697_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_691_, v___x_695_, v___x_696_, v_x_657_, v_x_658_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_697_);
v___x_699_ = v___x_693_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v___y_674_ = v___x_699_;
goto v___jp_673_;
}
}
}
default: 
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_x_657_);
lean_ctor_set(v___x_702_, 1, v_x_658_);
v___y_674_ = v___x_702_;
goto v___jp_673_;
}
}
v___jp_673_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_array_fset(v_xs_x27_672_, v_j_664_, v___y_674_);
lean_dec(v_j_664_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_675_);
v___x_677_ = v___x_668_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
else
{
lean_object* v_ks_705_; lean_object* v_vs_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_726_; 
v_ks_705_ = lean_ctor_get(v_x_654_, 0);
v_vs_706_ = lean_ctor_get(v_x_654_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_726_ == 0)
{
v___x_708_ = v_x_654_;
v_isShared_709_ = v_isSharedCheck_726_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_vs_706_);
lean_inc(v_ks_705_);
lean_dec(v_x_654_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_726_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_ks_705_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_vs_706_);
v___x_711_ = v_reuseFailAlloc_725_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v_newNode_712_; uint8_t v___y_714_; size_t v___x_720_; uint8_t v___x_721_; 
v_newNode_712_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_711_, v_x_657_, v_x_658_);
v___x_720_ = ((size_t)7ULL);
v___x_721_ = lean_usize_dec_le(v___x_720_, v_x_656_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_712_);
v___x_723_ = lean_unsigned_to_nat(4u);
v___x_724_ = lean_nat_dec_lt(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
v___y_714_ = v___x_724_;
goto v___jp_713_;
}
else
{
v___y_714_ = v___x_721_;
goto v___jp_713_;
}
v___jp_713_:
{
if (v___y_714_ == 0)
{
lean_object* v_ks_715_; lean_object* v_vs_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_ks_715_ = lean_ctor_get(v_newNode_712_, 0);
lean_inc_ref(v_ks_715_);
v_vs_716_ = lean_ctor_get(v_newNode_712_, 1);
lean_inc_ref(v_vs_716_);
lean_dec_ref(v_newNode_712_);
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__2);
v___x_719_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_656_, v_ks_715_, v_vs_716_, v___x_717_, v___x_718_);
lean_dec_ref(v_vs_716_);
lean_dec_ref(v_ks_715_);
return v___x_719_;
}
else
{
return v_newNode_712_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t v_depth_727_, lean_object* v_keys_728_, lean_object* v_vals_729_, lean_object* v_i_730_, lean_object* v_entries_731_){
_start:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_array_get_size(v_keys_728_);
v___x_733_ = lean_nat_dec_lt(v_i_730_, v___x_732_);
if (v___x_733_ == 0)
{
lean_dec(v_i_730_);
return v_entries_731_;
}
else
{
lean_object* v_k_734_; lean_object* v_v_735_; uint64_t v___x_736_; size_t v_h_737_; size_t v___x_738_; lean_object* v___x_739_; size_t v___x_740_; size_t v___x_741_; size_t v___x_742_; size_t v_h_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_k_734_ = lean_array_fget_borrowed(v_keys_728_, v_i_730_);
v_v_735_ = lean_array_fget_borrowed(v_vals_729_, v_i_730_);
v___x_736_ = l_Lean_instHashableFVarId_hash(v_k_734_);
v_h_737_ = lean_uint64_to_usize(v___x_736_);
v___x_738_ = ((size_t)5ULL);
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = ((size_t)1ULL);
v___x_741_ = lean_usize_sub(v_depth_727_, v___x_740_);
v___x_742_ = lean_usize_mul(v___x_738_, v___x_741_);
v_h_743_ = lean_usize_shift_right(v_h_737_, v___x_742_);
v___x_744_ = lean_nat_add(v_i_730_, v___x_739_);
lean_dec(v_i_730_);
lean_inc(v_v_735_);
lean_inc(v_k_734_);
v___x_745_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_entries_731_, v_h_743_, v_depth_727_, v_k_734_, v_v_735_);
v_i_730_ = v___x_744_;
v_entries_731_ = v___x_745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_747_, lean_object* v_keys_748_, lean_object* v_vals_749_, lean_object* v_i_750_, lean_object* v_entries_751_){
_start:
{
size_t v_depth_boxed_752_; lean_object* v_res_753_; 
v_depth_boxed_752_ = lean_unbox_usize(v_depth_747_);
lean_dec(v_depth_747_);
v_res_753_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_boxed_752_, v_keys_748_, v_vals_749_, v_i_750_, v_entries_751_);
lean_dec_ref(v_vals_749_);
lean_dec_ref(v_keys_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
size_t v_x_371__boxed_759_; size_t v_x_372__boxed_760_; lean_object* v_res_761_; 
v_x_371__boxed_759_ = lean_unbox_usize(v_x_755_);
lean_dec(v_x_755_);
v_x_372__boxed_760_ = lean_unbox_usize(v_x_756_);
lean_dec(v_x_756_);
v_res_761_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_754_, v_x_371__boxed_759_, v_x_372__boxed_760_, v_x_757_, v_x_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
uint64_t v___x_765_; size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___x_765_ = l_Lean_instHashableFVarId_hash(v_x_763_);
v___x_766_ = lean_uint64_to_usize(v___x_765_);
v___x_767_ = ((size_t)1ULL);
v___x_768_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_762_, v___x_766_, v___x_767_, v_x_763_, v_x_764_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* v_lctx_769_, lean_object* v_fvarId_770_, lean_object* v_userName_771_, lean_object* v_type_772_, uint8_t v_bi_773_, uint8_t v_kind_774_){
_start:
{
lean_object* v_decls_775_; lean_object* v_fvarIdToDecl_776_; lean_object* v_auxDeclToFullName_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_789_; 
v_decls_775_ = lean_ctor_get(v_lctx_769_, 1);
v_fvarIdToDecl_776_ = lean_ctor_get(v_lctx_769_, 0);
v_auxDeclToFullName_777_ = lean_ctor_get(v_lctx_769_, 2);
v_isSharedCheck_789_ = !lean_is_exclusive(v_lctx_769_);
if (v_isSharedCheck_789_ == 0)
{
v___x_779_ = v_lctx_769_;
v_isShared_780_ = v_isSharedCheck_789_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_auxDeclToFullName_777_);
lean_inc(v_decls_775_);
lean_inc(v_fvarIdToDecl_776_);
lean_dec(v_lctx_769_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_789_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_size_781_; lean_object* v_decl_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v_size_781_ = lean_ctor_get(v_decls_775_, 2);
lean_inc(v_fvarId_770_);
lean_inc(v_size_781_);
v_decl_782_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_782_, 0, v_size_781_);
lean_ctor_set(v_decl_782_, 1, v_fvarId_770_);
lean_ctor_set(v_decl_782_, 2, v_userName_771_);
lean_ctor_set(v_decl_782_, 3, v_type_772_);
lean_ctor_set_uint8(v_decl_782_, sizeof(void*)*4, v_bi_773_);
lean_ctor_set_uint8(v_decl_782_, sizeof(void*)*4 + 1, v_kind_774_);
lean_inc_ref(v_decl_782_);
v___x_783_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_776_, v_fvarId_770_, v_decl_782_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v_decl_782_);
v___x_785_ = l_Lean_PersistentArray_push___redArg(v_decls_775_, v___x_784_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v___x_785_);
lean_ctor_set(v___x_779_, 0, v___x_783_);
v___x_787_ = v___x_779_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_auxDeclToFullName_777_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* v_lctx_790_, lean_object* v_fvarId_791_, lean_object* v_userName_792_, lean_object* v_type_793_, lean_object* v_bi_794_, lean_object* v_kind_795_){
_start:
{
uint8_t v_bi_boxed_796_; uint8_t v_kind_boxed_797_; lean_object* v_res_798_; 
v_bi_boxed_796_ = lean_unbox(v_bi_794_);
v_kind_boxed_797_ = lean_unbox(v_kind_795_);
v_res_798_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_790_, v_fvarId_791_, v_userName_792_, v_type_793_, v_bi_boxed_796_, v_kind_boxed_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object* v_00_u03b2_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_x_800_, v_x_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object* v_00_u03b2_804_, lean_object* v_x_805_, size_t v_x_806_, size_t v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_805_, v_x_806_, v_x_807_, v_x_808_, v_x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
size_t v_x_581__boxed_817_; size_t v_x_582__boxed_818_; lean_object* v_res_819_; 
v_x_581__boxed_817_ = lean_unbox_usize(v_x_813_);
lean_dec(v_x_813_);
v_x_582__boxed_818_ = lean_unbox_usize(v_x_814_);
lean_dec(v_x_814_);
v_res_819_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(v_00_u03b2_811_, v_x_812_, v_x_581__boxed_817_, v_x_582__boxed_818_, v_x_815_, v_x_816_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_820_, lean_object* v_n_821_, lean_object* v_k_822_, lean_object* v_v_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v_n_821_, v_k_822_, v_v_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_825_, size_t v_depth_826_, lean_object* v_keys_827_, lean_object* v_vals_828_, lean_object* v_heq_829_, lean_object* v_i_830_, lean_object* v_entries_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_826_, v_keys_827_, v_vals_828_, v_i_830_, v_entries_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_833_, lean_object* v_depth_834_, lean_object* v_keys_835_, lean_object* v_vals_836_, lean_object* v_heq_837_, lean_object* v_i_838_, lean_object* v_entries_839_){
_start:
{
size_t v_depth_boxed_840_; lean_object* v_res_841_; 
v_depth_boxed_840_ = lean_unbox_usize(v_depth_834_);
lean_dec(v_depth_834_);
v_res_841_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(v_00_u03b2_833_, v_depth_boxed_840_, v_keys_835_, v_vals_836_, v_heq_837_, v_i_838_, v_entries_839_);
lean_dec_ref(v_vals_836_);
lean_dec_ref(v_keys_835_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_x_843_, v_x_844_, v_x_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object* v_lctx_848_, lean_object* v_fvarId_849_, lean_object* v_userName_850_, lean_object* v_type_851_, uint8_t v_bi_852_){
_start:
{
uint8_t v___x_853_; lean_object* v___x_854_; 
v___x_853_ = 0;
v___x_854_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_848_, v_fvarId_849_, v_userName_850_, v_type_851_, v_bi_852_, v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* v_lctx_855_, lean_object* v_fvarId_856_, lean_object* v_userName_857_, lean_object* v_type_858_, lean_object* v_bi_859_){
_start:
{
uint8_t v_bi_boxed_860_; lean_object* v_res_861_; 
v_bi_boxed_860_ = lean_unbox(v_bi_859_);
v_res_861_ = lean_local_ctx_mk_local_decl(v_lctx_855_, v_fvarId_856_, v_userName_857_, v_type_858_, v_bi_boxed_860_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* v_lctx_862_, lean_object* v_fvarId_863_, lean_object* v_userName_864_, lean_object* v_type_865_, lean_object* v_value_866_, uint8_t v_nondep_867_, uint8_t v_kind_868_){
_start:
{
lean_object* v_decls_869_; lean_object* v_fvarIdToDecl_870_; lean_object* v_auxDeclToFullName_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_883_; 
v_decls_869_ = lean_ctor_get(v_lctx_862_, 1);
v_fvarIdToDecl_870_ = lean_ctor_get(v_lctx_862_, 0);
v_auxDeclToFullName_871_ = lean_ctor_get(v_lctx_862_, 2);
v_isSharedCheck_883_ = !lean_is_exclusive(v_lctx_862_);
if (v_isSharedCheck_883_ == 0)
{
v___x_873_ = v_lctx_862_;
v_isShared_874_ = v_isSharedCheck_883_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_auxDeclToFullName_871_);
lean_inc(v_decls_869_);
lean_inc(v_fvarIdToDecl_870_);
lean_dec(v_lctx_862_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_883_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_size_875_; lean_object* v_decl_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v_size_875_ = lean_ctor_get(v_decls_869_, 2);
lean_inc(v_fvarId_863_);
lean_inc(v_size_875_);
v_decl_876_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_decl_876_, 0, v_size_875_);
lean_ctor_set(v_decl_876_, 1, v_fvarId_863_);
lean_ctor_set(v_decl_876_, 2, v_userName_864_);
lean_ctor_set(v_decl_876_, 3, v_type_865_);
lean_ctor_set(v_decl_876_, 4, v_value_866_);
lean_ctor_set_uint8(v_decl_876_, sizeof(void*)*5, v_nondep_867_);
lean_ctor_set_uint8(v_decl_876_, sizeof(void*)*5 + 1, v_kind_868_);
lean_inc_ref(v_decl_876_);
v___x_877_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_870_, v_fvarId_863_, v_decl_876_);
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v_decl_876_);
v___x_879_ = l_Lean_PersistentArray_push___redArg(v_decls_869_, v___x_878_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 1, v___x_879_);
lean_ctor_set(v___x_873_, 0, v___x_877_);
v___x_881_ = v___x_873_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_auxDeclToFullName_871_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* v_lctx_884_, lean_object* v_fvarId_885_, lean_object* v_userName_886_, lean_object* v_type_887_, lean_object* v_value_888_, lean_object* v_nondep_889_, lean_object* v_kind_890_){
_start:
{
uint8_t v_nondep_boxed_891_; uint8_t v_kind_boxed_892_; lean_object* v_res_893_; 
v_nondep_boxed_891_ = lean_unbox(v_nondep_889_);
v_kind_boxed_892_ = lean_unbox(v_kind_890_);
v_res_893_ = l_Lean_LocalContext_mkLetDecl(v_lctx_884_, v_fvarId_885_, v_userName_886_, v_type_887_, v_value_888_, v_nondep_boxed_891_, v_kind_boxed_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object* v_lctx_894_, lean_object* v_fvarId_895_, lean_object* v_userName_896_, lean_object* v_type_897_, lean_object* v_value_898_, uint8_t v_nondep_899_){
_start:
{
uint8_t v___x_900_; lean_object* v___x_901_; 
v___x_900_ = 0;
v___x_901_ = l_Lean_LocalContext_mkLetDecl(v_lctx_894_, v_fvarId_895_, v_userName_896_, v_type_897_, v_value_898_, v_nondep_899_, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* v_lctx_902_, lean_object* v_fvarId_903_, lean_object* v_userName_904_, lean_object* v_type_905_, lean_object* v_value_906_, lean_object* v_nondep_907_){
_start:
{
uint8_t v_nondep_boxed_908_; lean_object* v_res_909_; 
v_nondep_boxed_908_ = lean_unbox(v_nondep_907_);
v_res_909_ = lean_local_ctx_mk_let_decl(v_lctx_902_, v_fvarId_903_, v_userName_904_, v_type_905_, v_value_906_, v_nondep_boxed_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* v_lctx_910_, lean_object* v_fvarId_911_, lean_object* v_userName_912_, lean_object* v_type_913_, lean_object* v_fullName_914_){
_start:
{
lean_object* v_decls_915_; lean_object* v_fvarIdToDecl_916_; lean_object* v_auxDeclToFullName_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_932_; 
v_decls_915_ = lean_ctor_get(v_lctx_910_, 1);
v_fvarIdToDecl_916_ = lean_ctor_get(v_lctx_910_, 0);
v_auxDeclToFullName_917_ = lean_ctor_get(v_lctx_910_, 2);
v_isSharedCheck_932_ = !lean_is_exclusive(v_lctx_910_);
if (v_isSharedCheck_932_ == 0)
{
v___x_919_ = v_lctx_910_;
v_isShared_920_ = v_isSharedCheck_932_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_auxDeclToFullName_917_);
lean_inc(v_decls_915_);
lean_inc(v_fvarIdToDecl_916_);
lean_dec(v_lctx_910_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_932_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v_size_921_; uint8_t v___x_922_; uint8_t v___x_923_; lean_object* v_decl_924_; lean_object* v_auxDeclToFullName_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v_size_921_ = lean_ctor_get(v_decls_915_, 2);
v___x_922_ = 0;
v___x_923_ = 2;
lean_inc_n(v_fvarId_911_, 2);
lean_inc(v_size_921_);
v_decl_924_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_924_, 0, v_size_921_);
lean_ctor_set(v_decl_924_, 1, v_fvarId_911_);
lean_ctor_set(v_decl_924_, 2, v_userName_912_);
lean_ctor_set(v_decl_924_, 3, v_type_913_);
lean_ctor_set_uint8(v_decl_924_, sizeof(void*)*4, v___x_922_);
lean_ctor_set_uint8(v_decl_924_, sizeof(void*)*4 + 1, v___x_923_);
v_auxDeclToFullName_925_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_911_, v_fullName_914_, v_auxDeclToFullName_917_);
lean_inc_ref(v_decl_924_);
v___x_926_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_916_, v_fvarId_911_, v_decl_924_);
v___x_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_927_, 0, v_decl_924_);
v___x_928_ = l_Lean_PersistentArray_push___redArg(v_decls_915_, v___x_927_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 2, v_auxDeclToFullName_925_);
lean_ctor_set(v___x_919_, 1, v___x_928_);
lean_ctor_set(v___x_919_, 0, v___x_926_);
v___x_930_ = v___x_919_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_auxDeclToFullName_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* v_lctx_933_, lean_object* v_newDecl_934_){
_start:
{
lean_object* v_decls_935_; lean_object* v_fvarIdToDecl_936_; lean_object* v_auxDeclToFullName_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_952_; 
v_decls_935_ = lean_ctor_get(v_lctx_933_, 1);
v_fvarIdToDecl_936_ = lean_ctor_get(v_lctx_933_, 0);
v_auxDeclToFullName_937_ = lean_ctor_get(v_lctx_933_, 2);
v_isSharedCheck_952_ = !lean_is_exclusive(v_lctx_933_);
if (v_isSharedCheck_952_ == 0)
{
v___x_939_ = v_lctx_933_;
v_isShared_940_ = v_isSharedCheck_952_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_auxDeclToFullName_937_);
lean_inc(v_decls_935_);
lean_inc(v_fvarIdToDecl_936_);
lean_dec(v_lctx_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_952_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_size_941_; lean_object* v_newDecl_942_; lean_object* v___y_944_; lean_object* v_fvarId_951_; 
v_size_941_ = lean_ctor_get(v_decls_935_, 2);
lean_inc(v_size_941_);
v_newDecl_942_ = l_Lean_LocalDecl_setIndex(v_newDecl_934_, v_size_941_);
v_fvarId_951_ = lean_ctor_get(v_newDecl_942_, 1);
lean_inc(v_fvarId_951_);
v___y_944_ = v_fvarId_951_;
goto v___jp_943_;
v___jp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
lean_inc_ref(v_newDecl_942_);
v___x_945_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_936_, v___y_944_, v_newDecl_942_);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v_newDecl_942_);
v___x_947_ = l_Lean_PersistentArray_push___redArg(v_decls_935_, v___x_946_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_947_);
lean_ctor_set(v___x_939_, 0, v___x_945_);
v___x_949_ = v___x_939_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_auxDeclToFullName_937_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_953_, lean_object* v_vals_954_, lean_object* v_i_955_, lean_object* v_k_956_){
_start:
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_array_get_size(v_keys_953_);
v___x_958_ = lean_nat_dec_lt(v_i_955_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
lean_dec(v_i_955_);
v___x_959_ = lean_box(0);
return v___x_959_;
}
else
{
lean_object* v_k_x27_960_; uint8_t v___x_961_; 
v_k_x27_960_ = lean_array_fget_borrowed(v_keys_953_, v_i_955_);
v___x_961_ = l_Lean_instBEqFVarId_beq(v_k_956_, v_k_x27_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_add(v_i_955_, v___x_962_);
lean_dec(v_i_955_);
v_i_955_ = v___x_963_;
goto _start;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = lean_array_fget_borrowed(v_vals_954_, v_i_955_);
lean_dec(v_i_955_);
lean_inc(v___x_965_);
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_967_, lean_object* v_vals_968_, lean_object* v_i_969_, lean_object* v_k_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_967_, v_vals_968_, v_i_969_, v_k_970_);
lean_dec(v_k_970_);
lean_dec_ref(v_vals_968_);
lean_dec_ref(v_keys_967_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_972_, size_t v_x_973_, lean_object* v_x_974_){
_start:
{
if (lean_obj_tag(v_x_972_) == 0)
{
lean_object* v_es_975_; lean_object* v___x_976_; size_t v___x_977_; size_t v___x_978_; size_t v___x_979_; lean_object* v_j_980_; lean_object* v___x_981_; 
v_es_975_ = lean_ctor_get(v_x_972_, 0);
v___x_976_ = lean_box(2);
v___x_977_ = ((size_t)5ULL);
v___x_978_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_979_ = lean_usize_land(v_x_973_, v___x_978_);
v_j_980_ = lean_usize_to_nat(v___x_979_);
v___x_981_ = lean_array_get_borrowed(v___x_976_, v_es_975_, v_j_980_);
lean_dec(v_j_980_);
switch(lean_obj_tag(v___x_981_))
{
case 0:
{
lean_object* v_key_982_; lean_object* v_val_983_; uint8_t v___x_984_; 
v_key_982_ = lean_ctor_get(v___x_981_, 0);
v_val_983_ = lean_ctor_get(v___x_981_, 1);
v___x_984_ = l_Lean_instBEqFVarId_beq(v_x_974_, v_key_982_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = lean_box(0);
return v___x_985_;
}
else
{
lean_object* v___x_986_; 
lean_inc(v_val_983_);
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v_val_983_);
return v___x_986_;
}
}
case 1:
{
lean_object* v_node_987_; size_t v___x_988_; 
v_node_987_ = lean_ctor_get(v___x_981_, 0);
v___x_988_ = lean_usize_shift_right(v_x_973_, v___x_977_);
v_x_972_ = v_node_987_;
v_x_973_ = v___x_988_;
goto _start;
}
default: 
{
lean_object* v___x_990_; 
v___x_990_ = lean_box(0);
return v___x_990_;
}
}
}
else
{
lean_object* v_ks_991_; lean_object* v_vs_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_ks_991_ = lean_ctor_get(v_x_972_, 0);
v_vs_992_ = lean_ctor_get(v_x_972_, 1);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_991_, v_vs_992_, v___x_993_, v_x_974_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
size_t v_x_143__boxed_998_; lean_object* v_res_999_; 
v_x_143__boxed_998_ = lean_unbox_usize(v_x_996_);
lean_dec(v_x_996_);
v_res_999_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_995_, v_x_143__boxed_998_, v_x_997_);
lean_dec(v_x_997_);
lean_dec_ref(v_x_995_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
uint64_t v___x_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = l_Lean_instHashableFVarId_hash(v_x_1001_);
v___x_1003_ = lean_uint64_to_usize(v___x_1002_);
v___x_1004_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1000_, v___x_1003_, v_x_1001_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1005_, v_x_1006_);
lean_dec(v_x_1006_);
lean_dec_ref(v_x_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* v_lctx_1008_, lean_object* v_fvarId_1009_){
_start:
{
lean_object* v_fvarIdToDecl_1010_; lean_object* v___x_1011_; 
v_fvarIdToDecl_1010_ = lean_ctor_get(v_lctx_1008_, 0);
lean_inc_ref(v_fvarIdToDecl_1010_);
lean_dec_ref(v_lctx_1008_);
v___x_1011_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_1010_, v_fvarId_1009_);
lean_dec(v_fvarId_1009_);
lean_dec_ref(v_fvarIdToDecl_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object* v_00_u03b2_1012_, lean_object* v_x_1013_, lean_object* v_x_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1013_, v_x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(v_00_u03b2_1016_, v_x_1017_, v_x_1018_);
lean_dec(v_x_1018_);
lean_dec_ref(v_x_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1020_, lean_object* v_x_1021_, size_t v_x_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1021_, v_x_1022_, v_x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
size_t v_x_214__boxed_1029_; lean_object* v_res_1030_; 
v_x_214__boxed_1029_ = lean_unbox_usize(v_x_1027_);
lean_dec(v_x_1027_);
v_res_1030_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1025_, v_x_1026_, v_x_214__boxed_1029_, v_x_1028_);
lean_dec(v_x_1028_);
lean_dec_ref(v_x_1026_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1031_, lean_object* v_keys_1032_, lean_object* v_vals_1033_, lean_object* v_heq_1034_, lean_object* v_i_1035_, lean_object* v_k_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1032_, v_vals_1033_, v_i_1035_, v_k_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1038_, lean_object* v_keys_1039_, lean_object* v_vals_1040_, lean_object* v_heq_1041_, lean_object* v_i_1042_, lean_object* v_k_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1038_, v_keys_1039_, v_vals_1040_, v_heq_1041_, v_i_1042_, v_k_1043_);
lean_dec(v_k_1043_);
lean_dec_ref(v_vals_1040_);
lean_dec_ref(v_keys_1039_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* v_lctx_1045_, lean_object* v_e_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = l_Lean_Expr_fvarId_x21(v_e_1046_);
v___x_1048_ = lean_local_ctx_find(v_lctx_1045_, v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* v_lctx_1049_, lean_object* v_e_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_1049_, v_e_1050_);
lean_dec_ref(v_e_1050_);
return v_res_1051_;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1054_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_1055_ = lean_unsigned_to_nat(14u);
v___x_1056_ = lean_unsigned_to_nat(340u);
v___x_1057_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__0));
v___x_1058_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_1059_ = l_mkPanicMessageWithDecl(v___x_1058_, v___x_1057_, v___x_1056_, v___x_1055_, v___x_1054_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* v_lctx_1060_, lean_object* v_fvarId_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_local_ctx_find(v_lctx_1060_, v_fvarId_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_obj_once(&l_Lean_LocalContext_get_x21___closed__2, &l_Lean_LocalContext_get_x21___closed__2_once, _init_l_Lean_LocalContext_get_x21___closed__2);
v___x_1064_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_1063_);
return v___x_1064_;
}
else
{
lean_object* v_val_1065_; 
v_val_1065_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_val_1065_);
lean_dec_ref(v___x_1062_);
return v_val_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* v_lctx_1066_, lean_object* v_e_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = l_Lean_Expr_fvarId_x21(v_e_1067_);
v___x_1069_ = l_Lean_LocalContext_get_x21(v_lctx_1066_, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* v_lctx_1070_, lean_object* v_e_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1070_, v_e_1071_);
lean_dec_ref(v_e_1071_);
return v_res_1072_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1073_, lean_object* v_i_1074_, lean_object* v_k_1075_){
_start:
{
lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = lean_array_get_size(v_keys_1073_);
v___x_1077_ = lean_nat_dec_lt(v_i_1074_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_dec(v_i_1074_);
return v___x_1077_;
}
else
{
lean_object* v_k_x27_1078_; uint8_t v___x_1079_; 
v_k_x27_1078_ = lean_array_fget_borrowed(v_keys_1073_, v_i_1074_);
v___x_1079_ = l_Lean_instBEqFVarId_beq(v_k_1075_, v_k_x27_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = lean_nat_add(v_i_1074_, v___x_1080_);
lean_dec(v_i_1074_);
v_i_1074_ = v___x_1081_;
goto _start;
}
else
{
lean_dec(v_i_1074_);
return v___x_1079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1083_, lean_object* v_i_1084_, lean_object* v_k_1085_){
_start:
{
uint8_t v_res_1086_; lean_object* v_r_1087_; 
v_res_1086_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1083_, v_i_1084_, v_k_1085_);
lean_dec(v_k_1085_);
lean_dec_ref(v_keys_1083_);
v_r_1087_ = lean_box(v_res_1086_);
return v_r_1087_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object* v_x_1088_, size_t v_x_1089_, lean_object* v_x_1090_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
lean_object* v_es_1091_; lean_object* v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; lean_object* v_j_1096_; lean_object* v___x_1097_; 
v_es_1091_ = lean_ctor_get(v_x_1088_, 0);
v___x_1092_ = lean_box(2);
v___x_1093_ = ((size_t)5ULL);
v___x_1094_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_1095_ = lean_usize_land(v_x_1089_, v___x_1094_);
v_j_1096_ = lean_usize_to_nat(v___x_1095_);
v___x_1097_ = lean_array_get_borrowed(v___x_1092_, v_es_1091_, v_j_1096_);
lean_dec(v_j_1096_);
switch(lean_obj_tag(v___x_1097_))
{
case 0:
{
lean_object* v_key_1098_; uint8_t v___x_1099_; 
v_key_1098_ = lean_ctor_get(v___x_1097_, 0);
v___x_1099_ = l_Lean_instBEqFVarId_beq(v_x_1090_, v_key_1098_);
return v___x_1099_;
}
case 1:
{
lean_object* v_node_1100_; size_t v___x_1101_; 
v_node_1100_ = lean_ctor_get(v___x_1097_, 0);
v___x_1101_ = lean_usize_shift_right(v_x_1089_, v___x_1093_);
v_x_1088_ = v_node_1100_;
v_x_1089_ = v___x_1101_;
goto _start;
}
default: 
{
uint8_t v___x_1103_; 
v___x_1103_ = 0;
return v___x_1103_;
}
}
}
else
{
lean_object* v_ks_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v_ks_1104_ = lean_ctor_get(v_x_1088_, 0);
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_ks_1104_, v___x_1105_, v_x_1090_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
size_t v_x_129__boxed_1110_; uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_x_129__boxed_1110_ = lean_unbox_usize(v_x_1108_);
lean_dec(v_x_1108_);
v_res_1111_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1107_, v_x_129__boxed_1110_, v_x_1109_);
lean_dec(v_x_1109_);
lean_dec_ref(v_x_1107_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
uint64_t v___x_1115_; size_t v___x_1116_; uint8_t v___x_1117_; 
v___x_1115_ = l_Lean_instHashableFVarId_hash(v_x_1114_);
v___x_1116_ = lean_uint64_to_usize(v___x_1115_);
v___x_1117_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1113_, v___x_1116_, v_x_1114_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
uint8_t v_res_1120_; lean_object* v_r_1121_; 
v_res_1120_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1118_, v_x_1119_);
lean_dec(v_x_1119_);
lean_dec_ref(v_x_1118_);
v_r_1121_ = lean_box(v_res_1120_);
return v_r_1121_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object* v_lctx_1122_, lean_object* v_fvarId_1123_){
_start:
{
lean_object* v_fvarIdToDecl_1124_; uint8_t v___x_1125_; 
v_fvarIdToDecl_1124_ = lean_ctor_get(v_lctx_1122_, 0);
v___x_1125_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_fvarIdToDecl_1124_, v_fvarId_1123_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* v_lctx_1126_, lean_object* v_fvarId_1127_){
_start:
{
uint8_t v_res_1128_; lean_object* v_r_1129_; 
v_res_1128_ = l_Lean_LocalContext_contains(v_lctx_1126_, v_fvarId_1127_);
lean_dec(v_fvarId_1127_);
lean_dec_ref(v_lctx_1126_);
v_r_1129_ = lean_box(v_res_1128_);
return v_r_1129_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object* v_00_u03b2_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_){
_start:
{
uint8_t v___x_1133_; 
v___x_1133_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1131_, v_x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object* v_00_u03b2_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
uint8_t v_res_1137_; lean_object* v_r_1138_; 
v_res_1137_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(v_00_u03b2_1134_, v_x_1135_, v_x_1136_);
lean_dec(v_x_1136_);
lean_dec_ref(v_x_1135_);
v_r_1138_ = lean_box(v_res_1137_);
return v_r_1138_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object* v_00_u03b2_1139_, lean_object* v_x_1140_, size_t v_x_1141_, lean_object* v_x_1142_){
_start:
{
uint8_t v___x_1143_; 
v___x_1143_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1140_, v_x_1141_, v_x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_){
_start:
{
size_t v_x_194__boxed_1148_; uint8_t v_res_1149_; lean_object* v_r_1150_; 
v_x_194__boxed_1148_ = lean_unbox_usize(v_x_1146_);
lean_dec(v_x_1146_);
v_res_1149_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(v_00_u03b2_1144_, v_x_1145_, v_x_194__boxed_1148_, v_x_1147_);
lean_dec(v_x_1147_);
lean_dec_ref(v_x_1145_);
v_r_1150_ = lean_box(v_res_1149_);
return v_r_1150_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1151_, lean_object* v_keys_1152_, lean_object* v_vals_1153_, lean_object* v_heq_1154_, lean_object* v_i_1155_, lean_object* v_k_1156_){
_start:
{
uint8_t v___x_1157_; 
v___x_1157_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1152_, v_i_1155_, v_k_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1158_, lean_object* v_keys_1159_, lean_object* v_vals_1160_, lean_object* v_heq_1161_, lean_object* v_i_1162_, lean_object* v_k_1163_){
_start:
{
uint8_t v_res_1164_; lean_object* v_r_1165_; 
v_res_1164_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(v_00_u03b2_1158_, v_keys_1159_, v_vals_1160_, v_heq_1161_, v_i_1162_, v_k_1163_);
lean_dec(v_k_1163_);
lean_dec_ref(v_vals_1160_);
lean_dec_ref(v_keys_1159_);
v_r_1165_ = lean_box(v_res_1164_);
return v_r_1165_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object* v_lctx_1166_, lean_object* v_e_1167_){
_start:
{
lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = l_Lean_Expr_fvarId_x21(v_e_1167_);
v___x_1169_ = l_Lean_LocalContext_contains(v_lctx_1166_, v___x_1168_);
lean_dec(v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* v_lctx_1170_, lean_object* v_e_1171_){
_start:
{
uint8_t v_res_1172_; lean_object* v_r_1173_; 
v_res_1172_ = l_Lean_LocalContext_containsFVar(v_lctx_1170_, v_e_1171_);
lean_dec_ref(v_e_1171_);
lean_dec_ref(v_lctx_1170_);
v_r_1173_ = lean_box(v_res_1172_);
return v_r_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object* v_as_1174_, size_t v_i_1175_, size_t v_stop_1176_, lean_object* v_b_1177_){
_start:
{
lean_object* v___y_1179_; uint8_t v___x_1183_; 
v___x_1183_ = lean_usize_dec_eq(v_i_1175_, v_stop_1176_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_array_uget_borrowed(v_as_1174_, v_i_1175_);
if (lean_obj_tag(v___x_1184_) == 0)
{
v___y_1179_ = v_b_1177_;
goto v___jp_1178_;
}
else
{
lean_object* v_val_1185_; lean_object* v_fvarId_1186_; lean_object* v___x_1187_; 
v_val_1185_ = lean_ctor_get(v___x_1184_, 0);
v_fvarId_1186_ = lean_ctor_get(v_val_1185_, 1);
lean_inc(v_fvarId_1186_);
v___x_1187_ = lean_array_push(v_b_1177_, v_fvarId_1186_);
v___y_1179_ = v___x_1187_;
goto v___jp_1178_;
}
}
else
{
return v_b_1177_;
}
v___jp_1178_:
{
size_t v___x_1180_; size_t v___x_1181_; 
v___x_1180_ = ((size_t)1ULL);
v___x_1181_ = lean_usize_add(v_i_1175_, v___x_1180_);
v_i_1175_ = v___x_1181_;
v_b_1177_ = v___y_1179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object* v_as_1188_, lean_object* v_i_1189_, lean_object* v_stop_1190_, lean_object* v_b_1191_){
_start:
{
size_t v_i_boxed_1192_; size_t v_stop_boxed_1193_; lean_object* v_res_1194_; 
v_i_boxed_1192_ = lean_unbox_usize(v_i_1189_);
lean_dec(v_i_1189_);
v_stop_boxed_1193_ = lean_unbox_usize(v_stop_1190_);
lean_dec(v_stop_1190_);
v_res_1194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1188_, v_i_boxed_1192_, v_stop_boxed_1193_, v_b_1191_);
lean_dec_ref(v_as_1188_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object* v_x_1195_, lean_object* v_x_1196_){
_start:
{
if (lean_obj_tag(v_x_1195_) == 0)
{
lean_object* v_cs_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_cs_1197_ = lean_ctor_get(v_x_1195_, 0);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_array_get_size(v_cs_1197_);
v___x_1200_ = lean_nat_dec_lt(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
return v_x_1196_;
}
else
{
uint8_t v___x_1201_; 
v___x_1201_ = lean_nat_dec_le(v___x_1199_, v___x_1199_);
if (v___x_1201_ == 0)
{
if (v___x_1200_ == 0)
{
return v_x_1196_;
}
else
{
size_t v___x_1202_; size_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = ((size_t)0ULL);
v___x_1203_ = lean_usize_of_nat(v___x_1199_);
v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1197_, v___x_1202_, v___x_1203_, v_x_1196_);
return v___x_1204_;
}
}
else
{
size_t v___x_1205_; size_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = ((size_t)0ULL);
v___x_1206_ = lean_usize_of_nat(v___x_1199_);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1197_, v___x_1205_, v___x_1206_, v_x_1196_);
return v___x_1207_;
}
}
}
else
{
lean_object* v_vs_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_vs_1208_ = lean_ctor_get(v_x_1195_, 0);
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_array_get_size(v_vs_1208_);
v___x_1211_ = lean_nat_dec_lt(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
return v_x_1196_;
}
else
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_nat_dec_le(v___x_1210_, v___x_1210_);
if (v___x_1212_ == 0)
{
if (v___x_1211_ == 0)
{
return v_x_1196_;
}
else
{
size_t v___x_1213_; size_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = ((size_t)0ULL);
v___x_1214_ = lean_usize_of_nat(v___x_1210_);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1208_, v___x_1213_, v___x_1214_, v_x_1196_);
return v___x_1215_;
}
}
else
{
size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = ((size_t)0ULL);
v___x_1217_ = lean_usize_of_nat(v___x_1210_);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1208_, v___x_1216_, v___x_1217_, v_x_1196_);
return v___x_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1219_, size_t v_i_1220_, size_t v_stop_1221_, lean_object* v_b_1222_){
_start:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_usize_dec_eq(v_i_1220_, v_stop_1221_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; 
v___x_1224_ = lean_array_uget_borrowed(v_as_1219_, v_i_1220_);
v___x_1225_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1224_, v_b_1222_);
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_add(v_i_1220_, v___x_1226_);
v_i_1220_ = v___x_1227_;
v_b_1222_ = v___x_1225_;
goto _start;
}
else
{
return v_b_1222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1229_, lean_object* v_i_1230_, lean_object* v_stop_1231_, lean_object* v_b_1232_){
_start:
{
size_t v_i_boxed_1233_; size_t v_stop_boxed_1234_; lean_object* v_res_1235_; 
v_i_boxed_1233_ = lean_unbox_usize(v_i_1230_);
lean_dec(v_i_1230_);
v_stop_boxed_1234_ = lean_unbox_usize(v_stop_1231_);
lean_dec(v_stop_1231_);
v_res_1235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1229_, v_i_boxed_1233_, v_stop_boxed_1234_, v_b_1232_);
lean_dec_ref(v_as_1229_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1236_, lean_object* v_x_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1236_, v_x_1237_);
lean_dec_ref(v_x_1236_);
return v_res_1238_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1240_, size_t v_x_1241_, size_t v_x_1242_, lean_object* v_x_1243_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 0)
{
lean_object* v_cs_1244_; lean_object* v___x_1245_; size_t v___x_1246_; lean_object* v_j_1247_; lean_object* v___x_1248_; size_t v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; size_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_cs_1244_ = lean_ctor_get(v_x_1240_, 0);
v___x_1245_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1246_ = lean_usize_shift_right(v_x_1241_, v_x_1242_);
v_j_1247_ = lean_usize_to_nat(v___x_1246_);
v___x_1248_ = lean_array_get_borrowed(v___x_1245_, v_cs_1244_, v_j_1247_);
v___x_1249_ = ((size_t)1ULL);
v___x_1250_ = lean_usize_shift_left(v___x_1249_, v_x_1242_);
v___x_1251_ = lean_usize_sub(v___x_1250_, v___x_1249_);
v___x_1252_ = lean_usize_land(v_x_1241_, v___x_1251_);
v___x_1253_ = ((size_t)5ULL);
v___x_1254_ = lean_usize_sub(v_x_1242_, v___x_1253_);
v___x_1255_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1248_, v___x_1252_, v___x_1254_, v_x_1243_);
v___x_1256_ = lean_unsigned_to_nat(1u);
v___x_1257_ = lean_nat_add(v_j_1247_, v___x_1256_);
lean_dec(v_j_1247_);
v___x_1258_ = lean_array_get_size(v_cs_1244_);
v___x_1259_ = lean_nat_dec_lt(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_dec(v___x_1257_);
return v___x_1255_;
}
else
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_nat_dec_le(v___x_1258_, v___x_1258_);
if (v___x_1260_ == 0)
{
if (v___x_1259_ == 0)
{
lean_dec(v___x_1257_);
return v___x_1255_;
}
else
{
size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_usize_of_nat(v___x_1257_);
lean_dec(v___x_1257_);
v___x_1262_ = lean_usize_of_nat(v___x_1258_);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1244_, v___x_1261_, v___x_1262_, v___x_1255_);
return v___x_1263_;
}
}
else
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = lean_usize_of_nat(v___x_1257_);
lean_dec(v___x_1257_);
v___x_1265_ = lean_usize_of_nat(v___x_1258_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1244_, v___x_1264_, v___x_1265_, v___x_1255_);
return v___x_1266_;
}
}
}
else
{
lean_object* v_vs_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_vs_1267_ = lean_ctor_get(v_x_1240_, 0);
v___x_1268_ = lean_usize_to_nat(v_x_1241_);
v___x_1269_ = lean_array_get_size(v_vs_1267_);
v___x_1270_ = lean_nat_dec_lt(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_dec(v___x_1268_);
return v_x_1243_;
}
else
{
uint8_t v___x_1271_; 
v___x_1271_ = lean_nat_dec_le(v___x_1269_, v___x_1269_);
if (v___x_1271_ == 0)
{
if (v___x_1270_ == 0)
{
lean_dec(v___x_1268_);
return v_x_1243_;
}
else
{
size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = lean_usize_of_nat(v___x_1268_);
lean_dec(v___x_1268_);
v___x_1273_ = lean_usize_of_nat(v___x_1269_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1267_, v___x_1272_, v___x_1273_, v_x_1243_);
return v___x_1274_;
}
}
else
{
size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = lean_usize_of_nat(v___x_1268_);
lean_dec(v___x_1268_);
v___x_1276_ = lean_usize_of_nat(v___x_1269_);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1267_, v___x_1275_, v___x_1276_, v_x_1243_);
return v___x_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
size_t v_x_1632__boxed_1282_; size_t v_x_1633__boxed_1283_; lean_object* v_res_1284_; 
v_x_1632__boxed_1282_ = lean_unbox_usize(v_x_1279_);
lean_dec(v_x_1279_);
v_x_1633__boxed_1283_ = lean_unbox_usize(v_x_1280_);
lean_dec(v_x_1280_);
v_res_1284_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1278_, v_x_1632__boxed_1282_, v_x_1633__boxed_1283_, v_x_1281_);
lean_dec_ref(v_x_1278_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1285_, lean_object* v_init_1286_, lean_object* v_start_1287_){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_nat_dec_eq(v_start_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v_root_1290_; lean_object* v_tail_1291_; size_t v_shift_1292_; lean_object* v_tailOff_1293_; uint8_t v___x_1294_; 
v_root_1290_ = lean_ctor_get(v_t_1285_, 0);
v_tail_1291_ = lean_ctor_get(v_t_1285_, 1);
v_shift_1292_ = lean_ctor_get_usize(v_t_1285_, 4);
v_tailOff_1293_ = lean_ctor_get(v_t_1285_, 3);
v___x_1294_ = lean_nat_dec_le(v_tailOff_1293_, v_start_1287_);
if (v___x_1294_ == 0)
{
size_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1295_ = lean_usize_of_nat(v_start_1287_);
v___x_1296_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1290_, v___x_1295_, v_shift_1292_, v_init_1286_);
v___x_1297_ = lean_array_get_size(v_tail_1291_);
v___x_1298_ = lean_nat_dec_lt(v___x_1288_, v___x_1297_);
if (v___x_1298_ == 0)
{
return v___x_1296_;
}
else
{
uint8_t v___x_1299_; 
v___x_1299_ = lean_nat_dec_le(v___x_1297_, v___x_1297_);
if (v___x_1299_ == 0)
{
if (v___x_1298_ == 0)
{
return v___x_1296_;
}
else
{
size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = ((size_t)0ULL);
v___x_1301_ = lean_usize_of_nat(v___x_1297_);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1291_, v___x_1300_, v___x_1301_, v___x_1296_);
return v___x_1302_;
}
}
else
{
size_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = ((size_t)0ULL);
v___x_1304_ = lean_usize_of_nat(v___x_1297_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1291_, v___x_1303_, v___x_1304_, v___x_1296_);
return v___x_1305_;
}
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = lean_nat_sub(v_start_1287_, v_tailOff_1293_);
v___x_1307_ = lean_array_get_size(v_tail_1291_);
v___x_1308_ = lean_nat_dec_lt(v___x_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_dec(v___x_1306_);
return v_init_1286_;
}
else
{
uint8_t v___x_1309_; 
v___x_1309_ = lean_nat_dec_le(v___x_1307_, v___x_1307_);
if (v___x_1309_ == 0)
{
if (v___x_1308_ == 0)
{
lean_dec(v___x_1306_);
return v_init_1286_;
}
else
{
size_t v___x_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_usize_of_nat(v___x_1306_);
lean_dec(v___x_1306_);
v___x_1311_ = lean_usize_of_nat(v___x_1307_);
v___x_1312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1291_, v___x_1310_, v___x_1311_, v_init_1286_);
return v___x_1312_;
}
}
else
{
size_t v___x_1313_; size_t v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_usize_of_nat(v___x_1306_);
lean_dec(v___x_1306_);
v___x_1314_ = lean_usize_of_nat(v___x_1307_);
v___x_1315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1291_, v___x_1313_, v___x_1314_, v_init_1286_);
return v___x_1315_;
}
}
}
}
else
{
lean_object* v_root_1316_; lean_object* v_tail_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v_root_1316_ = lean_ctor_get(v_t_1285_, 0);
v_tail_1317_ = lean_ctor_get(v_t_1285_, 1);
v___x_1318_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1316_, v_init_1286_);
v___x_1319_ = lean_array_get_size(v_tail_1317_);
v___x_1320_ = lean_nat_dec_lt(v___x_1288_, v___x_1319_);
if (v___x_1320_ == 0)
{
return v___x_1318_;
}
else
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_nat_dec_le(v___x_1319_, v___x_1319_);
if (v___x_1321_ == 0)
{
if (v___x_1320_ == 0)
{
return v___x_1318_;
}
else
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = lean_usize_of_nat(v___x_1319_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1317_, v___x_1322_, v___x_1323_, v___x_1318_);
return v___x_1324_;
}
}
else
{
size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = lean_usize_of_nat(v___x_1319_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1317_, v___x_1325_, v___x_1326_, v___x_1318_);
return v___x_1327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1328_, lean_object* v_init_1329_, lean_object* v_start_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1328_, v_init_1329_, v_start_1330_);
lean_dec(v_start_1330_);
lean_dec_ref(v_t_1328_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1334_){
_start:
{
lean_object* v_decls_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_decls_1335_ = lean_ctor_get(v_lctx_1334_, 1);
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1338_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1335_, v___x_1337_, v___x_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_LocalContext_getFVarIds(v_lctx_1339_);
lean_dec_ref(v_lctx_1339_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1341_, size_t v_i_1342_, lean_object* v_bs_1343_){
_start:
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_usize_dec_lt(v_i_1342_, v_sz_1341_);
if (v___x_1344_ == 0)
{
return v_bs_1343_;
}
else
{
lean_object* v_v_1345_; lean_object* v___x_1346_; lean_object* v_bs_x27_1347_; lean_object* v___x_1348_; size_t v___x_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v_v_1345_ = lean_array_uget(v_bs_1343_, v_i_1342_);
v___x_1346_ = lean_unsigned_to_nat(0u);
v_bs_x27_1347_ = lean_array_uset(v_bs_1343_, v_i_1342_, v___x_1346_);
v___x_1348_ = l_Lean_mkFVar(v_v_1345_);
v___x_1349_ = ((size_t)1ULL);
v___x_1350_ = lean_usize_add(v_i_1342_, v___x_1349_);
v___x_1351_ = lean_array_uset(v_bs_x27_1347_, v_i_1342_, v___x_1348_);
v_i_1342_ = v___x_1350_;
v_bs_1343_ = v___x_1351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1353_, lean_object* v_i_1354_, lean_object* v_bs_1355_){
_start:
{
size_t v_sz_boxed_1356_; size_t v_i_boxed_1357_; lean_object* v_res_1358_; 
v_sz_boxed_1356_ = lean_unbox_usize(v_sz_1353_);
lean_dec(v_sz_1353_);
v_i_boxed_1357_ = lean_unbox_usize(v_i_1354_);
lean_dec(v_i_1354_);
v_res_1358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1356_, v_i_boxed_1357_, v_bs_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1359_){
_start:
{
lean_object* v___x_1360_; size_t v_sz_1361_; size_t v___x_1362_; lean_object* v___x_1363_; 
v___x_1360_ = l_Lean_LocalContext_getFVarIds(v_lctx_1359_);
v_sz_1361_ = lean_array_size(v___x_1360_);
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1361_, v___x_1362_, v___x_1360_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_LocalContext_getFVars(v_lctx_1364_);
lean_dec_ref(v_lctx_1364_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1366_){
_start:
{
lean_object* v_size_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_size_1367_ = lean_ctor_get(v_a_1366_, 2);
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_nat_dec_eq(v_size_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1370_ = lean_box(0);
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_sub(v_size_1367_, v___x_1371_);
v___x_1373_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1370_, v_a_1366_, v___x_1372_);
lean_dec(v___x_1372_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_PersistentArray_pop___redArg(v_a_1366_);
v_a_1366_ = v___x_1374_;
goto _start;
}
else
{
lean_dec_ref(v___x_1373_);
return v_a_1366_;
}
}
else
{
return v_a_1366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1376_, lean_object* v_t_1377_){
_start:
{
if (lean_obj_tag(v_t_1377_) == 0)
{
lean_object* v_k_1378_; lean_object* v_v_1379_; lean_object* v_l_1380_; lean_object* v_r_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_2035_; 
v_k_1378_ = lean_ctor_get(v_t_1377_, 1);
v_v_1379_ = lean_ctor_get(v_t_1377_, 2);
v_l_1380_ = lean_ctor_get(v_t_1377_, 3);
v_r_1381_ = lean_ctor_get(v_t_1377_, 4);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_t_1377_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v_t_1377_, 0);
lean_dec(v_unused_2036_);
v___x_1383_ = v_t_1377_;
v_isShared_1384_ = v_isSharedCheck_2035_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_r_1381_);
lean_inc(v_l_1380_);
lean_inc(v_v_1379_);
lean_inc(v_k_1378_);
lean_dec(v_t_1377_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_2035_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
uint8_t v___x_1385_; 
v___x_1385_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1376_, v_k_1378_);
switch(v___x_1385_)
{
case 0:
{
lean_object* v_impl_1386_; lean_object* v___x_1387_; 
v_impl_1386_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1376_, v_l_1380_);
v___x_1387_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1386_) == 0)
{
if (lean_obj_tag(v_r_1381_) == 0)
{
lean_object* v_size_1388_; lean_object* v_size_1389_; lean_object* v_k_1390_; lean_object* v_v_1391_; lean_object* v_l_1392_; lean_object* v_r_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_size_1388_ = lean_ctor_get(v_impl_1386_, 0);
lean_inc(v_size_1388_);
v_size_1389_ = lean_ctor_get(v_r_1381_, 0);
v_k_1390_ = lean_ctor_get(v_r_1381_, 1);
v_v_1391_ = lean_ctor_get(v_r_1381_, 2);
v_l_1392_ = lean_ctor_get(v_r_1381_, 3);
lean_inc(v_l_1392_);
v_r_1393_ = lean_ctor_get(v_r_1381_, 4);
v___x_1394_ = lean_unsigned_to_nat(3u);
v___x_1395_ = lean_nat_mul(v___x_1394_, v_size_1388_);
v___x_1396_ = lean_nat_dec_lt(v___x_1395_, v_size_1389_);
lean_dec(v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
lean_dec(v_l_1392_);
v___x_1397_ = lean_nat_add(v___x_1387_, v_size_1388_);
lean_dec(v_size_1388_);
v___x_1398_ = lean_nat_add(v___x_1397_, v_size_1389_);
lean_dec(v___x_1397_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 3, v_impl_1386_);
lean_ctor_set(v___x_1383_, 0, v___x_1398_);
v___x_1400_ = v___x_1383_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_impl_1386_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_r_1381_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
else
{
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1465_; 
lean_inc(v_r_1393_);
lean_inc(v_v_1391_);
lean_inc(v_k_1390_);
lean_inc(v_size_1389_);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_r_1381_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; lean_object* v_unused_1470_; 
v_unused_1466_ = lean_ctor_get(v_r_1381_, 4);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_r_1381_, 3);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_r_1381_, 2);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_r_1381_, 1);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_r_1381_, 0);
lean_dec(v_unused_1470_);
v___x_1403_ = v_r_1381_;
v_isShared_1404_ = v_isSharedCheck_1465_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v_r_1381_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1465_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v_size_1405_; lean_object* v_k_1406_; lean_object* v_v_1407_; lean_object* v_l_1408_; lean_object* v_r_1409_; lean_object* v_size_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v_size_1405_ = lean_ctor_get(v_l_1392_, 0);
v_k_1406_ = lean_ctor_get(v_l_1392_, 1);
v_v_1407_ = lean_ctor_get(v_l_1392_, 2);
v_l_1408_ = lean_ctor_get(v_l_1392_, 3);
v_r_1409_ = lean_ctor_get(v_l_1392_, 4);
v_size_1410_ = lean_ctor_get(v_r_1393_, 0);
v___x_1411_ = lean_unsigned_to_nat(2u);
v___x_1412_ = lean_nat_mul(v___x_1411_, v_size_1410_);
v___x_1413_ = lean_nat_dec_lt(v_size_1405_, v___x_1412_);
lean_dec(v___x_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1441_; 
lean_inc(v_r_1409_);
lean_inc(v_l_1408_);
lean_inc(v_v_1407_);
lean_inc(v_k_1406_);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_l_1392_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; lean_object* v_unused_1443_; lean_object* v_unused_1444_; lean_object* v_unused_1445_; lean_object* v_unused_1446_; 
v_unused_1442_ = lean_ctor_get(v_l_1392_, 4);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_l_1392_, 3);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_l_1392_, 2);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v_l_1392_, 1);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_l_1392_, 0);
lean_dec(v_unused_1446_);
v___x_1415_ = v_l_1392_;
v_isShared_1416_ = v_isSharedCheck_1441_;
goto v_resetjp_1414_;
}
else
{
lean_dec(v_l_1392_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1441_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1431_; 
v___x_1417_ = lean_nat_add(v___x_1387_, v_size_1388_);
lean_dec(v_size_1388_);
v___x_1418_ = lean_nat_add(v___x_1417_, v_size_1389_);
lean_dec(v_size_1389_);
if (lean_obj_tag(v_l_1408_) == 0)
{
lean_object* v_size_1439_; 
v_size_1439_ = lean_ctor_get(v_l_1408_, 0);
lean_inc(v_size_1439_);
v___y_1431_ = v_size_1439_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v___y_1431_ = v___x_1440_;
goto v___jp_1430_;
}
v___jp_1419_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_nat_add(v___y_1420_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec(v___y_1420_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v_r_1393_);
lean_ctor_set(v___x_1415_, 3, v_r_1409_);
lean_ctor_set(v___x_1415_, 2, v_v_1391_);
lean_ctor_set(v___x_1415_, 1, v_k_1390_);
lean_ctor_set(v___x_1415_, 0, v___x_1423_);
v___x_1425_ = v___x_1415_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_k_1390_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_v_1391_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v_r_1409_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v_r_1393_);
v___x_1425_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1427_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v___x_1425_);
lean_ctor_set(v___x_1403_, 3, v___y_1421_);
lean_ctor_set(v___x_1403_, 2, v_v_1407_);
lean_ctor_set(v___x_1403_, 1, v_k_1406_);
lean_ctor_set(v___x_1403_, 0, v___x_1418_);
v___x_1427_ = v___x_1403_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_k_1406_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_v_1407_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v___y_1421_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
v___jp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_nat_add(v___x_1417_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec(v___x_1417_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_l_1408_);
lean_ctor_set(v___x_1383_, 3, v_impl_1386_);
lean_ctor_set(v___x_1383_, 0, v___x_1432_);
v___x_1434_ = v___x_1383_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v_impl_1386_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v_l_1408_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_nat_add(v___x_1387_, v_size_1410_);
if (lean_obj_tag(v_r_1409_) == 0)
{
lean_object* v_size_1436_; 
v_size_1436_ = lean_ctor_get(v_r_1409_, 0);
lean_inc(v_size_1436_);
v___y_1420_ = v___x_1435_;
v___y_1421_ = v___x_1434_;
v___y_1422_ = v_size_1436_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_unsigned_to_nat(0u);
v___y_1420_ = v___x_1435_;
v___y_1421_ = v___x_1434_;
v___y_1422_ = v___x_1437_;
goto v___jp_1419_;
}
}
}
}
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
lean_del_object(v___x_1383_);
v___x_1447_ = lean_nat_add(v___x_1387_, v_size_1388_);
lean_dec(v_size_1388_);
v___x_1448_ = lean_nat_add(v___x_1447_, v_size_1389_);
lean_dec(v_size_1389_);
v___x_1449_ = lean_nat_add(v___x_1447_, v_size_1405_);
lean_dec(v___x_1447_);
lean_inc_ref(v_impl_1386_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v_l_1392_);
lean_ctor_set(v___x_1403_, 3, v_impl_1386_);
lean_ctor_set(v___x_1403_, 2, v_v_1379_);
lean_ctor_set(v___x_1403_, 1, v_k_1378_);
lean_ctor_set(v___x_1403_, 0, v___x_1449_);
v___x_1451_ = v___x_1403_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_impl_1386_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_l_1392_);
v___x_1451_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_isSharedCheck_1458_ = !lean_is_exclusive(v_impl_1386_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; lean_object* v_unused_1462_; lean_object* v_unused_1463_; 
v_unused_1459_ = lean_ctor_get(v_impl_1386_, 4);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_impl_1386_, 3);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_impl_1386_, 2);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_impl_1386_, 1);
lean_dec(v_unused_1462_);
v_unused_1463_ = lean_ctor_get(v_impl_1386_, 0);
lean_dec(v_unused_1463_);
v___x_1453_ = v_impl_1386_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_dec(v_impl_1386_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 4, v_r_1393_);
lean_ctor_set(v___x_1453_, 3, v___x_1451_);
lean_ctor_set(v___x_1453_, 2, v_v_1391_);
lean_ctor_set(v___x_1453_, 1, v_k_1390_);
lean_ctor_set(v___x_1453_, 0, v___x_1448_);
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_k_1390_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_v_1391_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_r_1393_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
v_size_1471_ = lean_ctor_get(v_impl_1386_, 0);
lean_inc(v_size_1471_);
v___x_1472_ = lean_nat_add(v___x_1387_, v_size_1471_);
lean_dec(v_size_1471_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 3, v_impl_1386_);
lean_ctor_set(v___x_1383_, 0, v___x_1472_);
v___x_1474_ = v___x_1383_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_impl_1386_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_r_1381_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
if (lean_obj_tag(v_r_1381_) == 0)
{
lean_object* v_l_1476_; 
v_l_1476_ = lean_ctor_get(v_r_1381_, 3);
lean_inc(v_l_1476_);
if (lean_obj_tag(v_l_1476_) == 0)
{
lean_object* v_r_1477_; 
v_r_1477_ = lean_ctor_get(v_r_1381_, 4);
lean_inc(v_r_1477_);
if (lean_obj_tag(v_r_1477_) == 0)
{
lean_object* v_size_1478_; lean_object* v_k_1479_; lean_object* v_v_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1493_; 
v_size_1478_ = lean_ctor_get(v_r_1381_, 0);
v_k_1479_ = lean_ctor_get(v_r_1381_, 1);
v_v_1480_ = lean_ctor_get(v_r_1381_, 2);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_r_1381_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; lean_object* v_unused_1495_; 
v_unused_1494_ = lean_ctor_get(v_r_1381_, 4);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_r_1381_, 3);
lean_dec(v_unused_1495_);
v___x_1482_ = v_r_1381_;
v_isShared_1483_ = v_isSharedCheck_1493_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_v_1480_);
lean_inc(v_k_1479_);
lean_inc(v_size_1478_);
lean_dec(v_r_1381_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1493_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_size_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v_size_1484_ = lean_ctor_get(v_l_1476_, 0);
v___x_1485_ = lean_nat_add(v___x_1387_, v_size_1478_);
lean_dec(v_size_1478_);
v___x_1486_ = lean_nat_add(v___x_1387_, v_size_1484_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v_l_1476_);
lean_ctor_set(v___x_1482_, 3, v_impl_1386_);
lean_ctor_set(v___x_1482_, 2, v_v_1379_);
lean_ctor_set(v___x_1482_, 1, v_k_1378_);
lean_ctor_set(v___x_1482_, 0, v___x_1486_);
v___x_1488_ = v___x_1482_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_impl_1386_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v_l_1476_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_r_1477_);
lean_ctor_set(v___x_1383_, 3, v___x_1488_);
lean_ctor_set(v___x_1383_, 2, v_v_1480_);
lean_ctor_set(v___x_1383_, 1, v_k_1479_);
lean_ctor_set(v___x_1383_, 0, v___x_1485_);
v___x_1490_ = v___x_1383_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v_r_1477_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v_k_1496_; lean_object* v_v_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1520_; 
v_k_1496_ = lean_ctor_get(v_r_1381_, 1);
v_v_1497_ = lean_ctor_get(v_r_1381_, 2);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_r_1381_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; 
v_unused_1521_ = lean_ctor_get(v_r_1381_, 4);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_r_1381_, 3);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_r_1381_, 0);
lean_dec(v_unused_1523_);
v___x_1499_ = v_r_1381_;
v_isShared_1500_ = v_isSharedCheck_1520_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_v_1497_);
lean_inc(v_k_1496_);
lean_dec(v_r_1381_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1520_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_k_1501_; lean_object* v_v_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1516_; 
v_k_1501_ = lean_ctor_get(v_l_1476_, 1);
v_v_1502_ = lean_ctor_get(v_l_1476_, 2);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_l_1476_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; 
v_unused_1517_ = lean_ctor_get(v_l_1476_, 4);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_l_1476_, 3);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_l_1476_, 0);
lean_dec(v_unused_1519_);
v___x_1504_ = v_l_1476_;
v_isShared_1505_ = v_isSharedCheck_1516_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_v_1502_);
lean_inc(v_k_1501_);
lean_dec(v_l_1476_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1516_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = lean_unsigned_to_nat(3u);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 4, v_r_1477_);
lean_ctor_set(v___x_1504_, 3, v_r_1477_);
lean_ctor_set(v___x_1504_, 2, v_v_1379_);
lean_ctor_set(v___x_1504_, 1, v_k_1378_);
lean_ctor_set(v___x_1504_, 0, v___x_1387_);
v___x_1508_ = v___x_1504_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v_r_1477_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_r_1477_);
v___x_1508_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1510_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 3, v_r_1477_);
lean_ctor_set(v___x_1499_, 0, v___x_1387_);
v___x_1510_ = v___x_1499_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_k_1496_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1497_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_r_1477_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_r_1477_);
v___x_1510_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v___x_1510_);
lean_ctor_set(v___x_1383_, 3, v___x_1508_);
lean_ctor_set(v___x_1383_, 2, v_v_1502_);
lean_ctor_set(v___x_1383_, 1, v_k_1501_);
lean_ctor_set(v___x_1383_, 0, v___x_1506_);
v___x_1512_ = v___x_1383_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_k_1501_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_v_1502_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1524_; 
v_r_1524_ = lean_ctor_get(v_r_1381_, 4);
lean_inc(v_r_1524_);
if (lean_obj_tag(v_r_1524_) == 0)
{
lean_object* v_k_1525_; lean_object* v_v_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1537_; 
v_k_1525_ = lean_ctor_get(v_r_1381_, 1);
v_v_1526_ = lean_ctor_get(v_r_1381_, 2);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_r_1381_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; 
v_unused_1538_ = lean_ctor_get(v_r_1381_, 4);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_r_1381_, 3);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_r_1381_, 0);
lean_dec(v_unused_1540_);
v___x_1528_ = v_r_1381_;
v_isShared_1529_ = v_isSharedCheck_1537_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_v_1526_);
lean_inc(v_k_1525_);
lean_dec(v_r_1381_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1537_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1530_ = lean_unsigned_to_nat(3u);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 4, v_l_1476_);
lean_ctor_set(v___x_1528_, 2, v_v_1379_);
lean_ctor_set(v___x_1528_, 1, v_k_1378_);
lean_ctor_set(v___x_1528_, 0, v___x_1387_);
v___x_1532_ = v___x_1528_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_l_1476_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_l_1476_);
v___x_1532_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_r_1524_);
lean_ctor_set(v___x_1383_, 3, v___x_1532_);
lean_ctor_set(v___x_1383_, 2, v_v_1526_);
lean_ctor_set(v___x_1383_, 1, v_k_1525_);
lean_ctor_set(v___x_1383_, 0, v___x_1530_);
v___x_1534_ = v___x_1383_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_k_1525_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_v_1526_);
lean_ctor_set(v_reuseFailAlloc_1535_, 3, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1535_, 4, v_r_1524_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v_size_1541_; lean_object* v_k_1542_; lean_object* v_v_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1554_; 
v_size_1541_ = lean_ctor_get(v_r_1381_, 0);
v_k_1542_ = lean_ctor_get(v_r_1381_, 1);
v_v_1543_ = lean_ctor_get(v_r_1381_, 2);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_r_1381_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; lean_object* v_unused_1556_; 
v_unused_1555_ = lean_ctor_get(v_r_1381_, 4);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_r_1381_, 3);
lean_dec(v_unused_1556_);
v___x_1545_ = v_r_1381_;
v_isShared_1546_ = v_isSharedCheck_1554_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_v_1543_);
lean_inc(v_k_1542_);
lean_inc(v_size_1541_);
lean_dec(v_r_1381_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1554_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 3, v_r_1524_);
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_size_1541_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_k_1542_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_v_1543_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_r_1524_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_r_1524_);
v___x_1548_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1549_ = lean_unsigned_to_nat(2u);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v___x_1548_);
lean_ctor_set(v___x_1383_, 3, v_r_1524_);
lean_ctor_set(v___x_1383_, 0, v___x_1549_);
v___x_1551_ = v___x_1383_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_r_1524_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v___x_1548_);
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
}
}
else
{
lean_object* v___x_1558_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 3, v_r_1381_);
lean_ctor_set(v___x_1383_, 0, v___x_1387_);
v___x_1558_ = v___x_1383_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_r_1381_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_r_1381_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1383_);
lean_dec(v_v_1379_);
lean_dec(v_k_1378_);
if (lean_obj_tag(v_l_1380_) == 0)
{
if (lean_obj_tag(v_r_1381_) == 0)
{
lean_object* v_size_1560_; lean_object* v_k_1561_; lean_object* v_v_1562_; lean_object* v_l_1563_; lean_object* v_r_1564_; lean_object* v_size_1565_; lean_object* v_k_1566_; lean_object* v_v_1567_; lean_object* v_l_1568_; lean_object* v_r_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v_size_1560_ = lean_ctor_get(v_l_1380_, 0);
v_k_1561_ = lean_ctor_get(v_l_1380_, 1);
v_v_1562_ = lean_ctor_get(v_l_1380_, 2);
v_l_1563_ = lean_ctor_get(v_l_1380_, 3);
v_r_1564_ = lean_ctor_get(v_l_1380_, 4);
lean_inc(v_r_1564_);
v_size_1565_ = lean_ctor_get(v_r_1381_, 0);
v_k_1566_ = lean_ctor_get(v_r_1381_, 1);
v_v_1567_ = lean_ctor_get(v_r_1381_, 2);
v_l_1568_ = lean_ctor_get(v_r_1381_, 3);
lean_inc(v_l_1568_);
v_r_1569_ = lean_ctor_get(v_r_1381_, 4);
v___x_1570_ = lean_unsigned_to_nat(1u);
v___x_1571_ = lean_nat_dec_lt(v_size_1560_, v_size_1565_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1707_; 
lean_inc(v_l_1563_);
lean_inc(v_v_1562_);
lean_inc(v_k_1561_);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_l_1380_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; lean_object* v_unused_1709_; lean_object* v_unused_1710_; lean_object* v_unused_1711_; lean_object* v_unused_1712_; 
v_unused_1708_ = lean_ctor_get(v_l_1380_, 4);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v_l_1380_, 3);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v_l_1380_, 2);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v_l_1380_, 1);
lean_dec(v_unused_1711_);
v_unused_1712_ = lean_ctor_get(v_l_1380_, 0);
lean_dec(v_unused_1712_);
v___x_1573_ = v_l_1380_;
v_isShared_1574_ = v_isSharedCheck_1707_;
goto v_resetjp_1572_;
}
else
{
lean_dec(v_l_1380_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1707_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v_tree_1576_; 
v___x_1575_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1561_, v_v_1562_, v_l_1563_, v_r_1564_);
v_tree_1576_ = lean_ctor_get(v___x_1575_, 2);
lean_inc(v_tree_1576_);
if (lean_obj_tag(v_tree_1576_) == 0)
{
lean_object* v_k_1577_; lean_object* v_v_1578_; lean_object* v_size_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v_k_1577_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_k_1577_);
v_v_1578_ = lean_ctor_get(v___x_1575_, 1);
lean_inc(v_v_1578_);
lean_dec_ref(v___x_1575_);
v_size_1579_ = lean_ctor_get(v_tree_1576_, 0);
v___x_1580_ = lean_unsigned_to_nat(3u);
v___x_1581_ = lean_nat_mul(v___x_1580_, v_size_1579_);
v___x_1582_ = lean_nat_dec_lt(v___x_1581_, v_size_1565_);
lean_dec(v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
lean_dec(v_l_1568_);
v___x_1583_ = lean_nat_add(v___x_1570_, v_size_1579_);
v___x_1584_ = lean_nat_add(v___x_1583_, v_size_1565_);
lean_dec(v___x_1583_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 4, v_r_1381_);
lean_ctor_set(v___x_1573_, 3, v_tree_1576_);
lean_ctor_set(v___x_1573_, 2, v_v_1578_);
lean_ctor_set(v___x_1573_, 1, v_k_1577_);
lean_ctor_set(v___x_1573_, 0, v___x_1584_);
v___x_1586_ = v___x_1573_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_k_1577_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_v_1578_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v_tree_1576_);
lean_ctor_set(v_reuseFailAlloc_1587_, 4, v_r_1381_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
else
{
lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1642_; 
lean_inc(v_r_1569_);
lean_inc(v_v_1567_);
lean_inc(v_k_1566_);
lean_inc(v_size_1565_);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_r_1381_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; lean_object* v_unused_1644_; lean_object* v_unused_1645_; lean_object* v_unused_1646_; lean_object* v_unused_1647_; 
v_unused_1643_ = lean_ctor_get(v_r_1381_, 4);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_r_1381_, 3);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_r_1381_, 2);
lean_dec(v_unused_1645_);
v_unused_1646_ = lean_ctor_get(v_r_1381_, 1);
lean_dec(v_unused_1646_);
v_unused_1647_ = lean_ctor_get(v_r_1381_, 0);
lean_dec(v_unused_1647_);
v___x_1589_ = v_r_1381_;
v_isShared_1590_ = v_isSharedCheck_1642_;
goto v_resetjp_1588_;
}
else
{
lean_dec(v_r_1381_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1642_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v_size_1591_; lean_object* v_k_1592_; lean_object* v_v_1593_; lean_object* v_l_1594_; lean_object* v_r_1595_; lean_object* v_size_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v_size_1591_ = lean_ctor_get(v_l_1568_, 0);
v_k_1592_ = lean_ctor_get(v_l_1568_, 1);
v_v_1593_ = lean_ctor_get(v_l_1568_, 2);
v_l_1594_ = lean_ctor_get(v_l_1568_, 3);
v_r_1595_ = lean_ctor_get(v_l_1568_, 4);
v_size_1596_ = lean_ctor_get(v_r_1569_, 0);
v___x_1597_ = lean_unsigned_to_nat(2u);
v___x_1598_ = lean_nat_mul(v___x_1597_, v_size_1596_);
v___x_1599_ = lean_nat_dec_lt(v_size_1591_, v___x_1598_);
lean_dec(v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1627_; 
lean_inc(v_r_1595_);
lean_inc(v_l_1594_);
lean_inc(v_v_1593_);
lean_inc(v_k_1592_);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_l_1568_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; lean_object* v_unused_1629_; lean_object* v_unused_1630_; lean_object* v_unused_1631_; lean_object* v_unused_1632_; 
v_unused_1628_ = lean_ctor_get(v_l_1568_, 4);
lean_dec(v_unused_1628_);
v_unused_1629_ = lean_ctor_get(v_l_1568_, 3);
lean_dec(v_unused_1629_);
v_unused_1630_ = lean_ctor_get(v_l_1568_, 2);
lean_dec(v_unused_1630_);
v_unused_1631_ = lean_ctor_get(v_l_1568_, 1);
lean_dec(v_unused_1631_);
v_unused_1632_ = lean_ctor_get(v_l_1568_, 0);
lean_dec(v_unused_1632_);
v___x_1601_ = v_l_1568_;
v_isShared_1602_ = v_isSharedCheck_1627_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v_l_1568_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1627_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1617_; 
v___x_1603_ = lean_nat_add(v___x_1570_, v_size_1579_);
v___x_1604_ = lean_nat_add(v___x_1603_, v_size_1565_);
lean_dec(v_size_1565_);
if (lean_obj_tag(v_l_1594_) == 0)
{
lean_object* v_size_1625_; 
v_size_1625_ = lean_ctor_get(v_l_1594_, 0);
lean_inc(v_size_1625_);
v___y_1617_ = v_size_1625_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_unsigned_to_nat(0u);
v___y_1617_ = v___x_1626_;
goto v___jp_1616_;
}
v___jp_1605_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_nat_add(v___y_1606_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec(v___y_1606_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 4, v_r_1569_);
lean_ctor_set(v___x_1601_, 3, v_r_1595_);
lean_ctor_set(v___x_1601_, 2, v_v_1567_);
lean_ctor_set(v___x_1601_, 1, v_k_1566_);
lean_ctor_set(v___x_1601_, 0, v___x_1609_);
v___x_1611_ = v___x_1601_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_r_1595_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_r_1569_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 4, v___x_1611_);
lean_ctor_set(v___x_1589_, 3, v___y_1607_);
lean_ctor_set(v___x_1589_, 2, v_v_1593_);
lean_ctor_set(v___x_1589_, 1, v_k_1592_);
lean_ctor_set(v___x_1589_, 0, v___x_1604_);
v___x_1613_ = v___x_1589_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_k_1592_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_v_1593_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v___y_1607_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
v___jp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1618_ = lean_nat_add(v___x_1603_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec(v___x_1603_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 4, v_l_1594_);
lean_ctor_set(v___x_1573_, 3, v_tree_1576_);
lean_ctor_set(v___x_1573_, 2, v_v_1578_);
lean_ctor_set(v___x_1573_, 1, v_k_1577_);
lean_ctor_set(v___x_1573_, 0, v___x_1618_);
v___x_1620_ = v___x_1573_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_k_1577_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_v_1578_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v_tree_1576_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v_l_1594_);
v___x_1620_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_nat_add(v___x_1570_, v_size_1596_);
if (lean_obj_tag(v_r_1595_) == 0)
{
lean_object* v_size_1622_; 
v_size_1622_ = lean_ctor_get(v_r_1595_, 0);
lean_inc(v_size_1622_);
v___y_1606_ = v___x_1621_;
v___y_1607_ = v___x_1620_;
v___y_1608_ = v_size_1622_;
goto v___jp_1605_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_unsigned_to_nat(0u);
v___y_1606_ = v___x_1621_;
v___y_1607_ = v___x_1620_;
v___y_1608_ = v___x_1623_;
goto v___jp_1605_;
}
}
}
}
}
else
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1633_ = lean_nat_add(v___x_1570_, v_size_1579_);
v___x_1634_ = lean_nat_add(v___x_1633_, v_size_1565_);
lean_dec(v_size_1565_);
v___x_1635_ = lean_nat_add(v___x_1633_, v_size_1591_);
lean_dec(v___x_1633_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 4, v_l_1568_);
lean_ctor_set(v___x_1589_, 3, v_tree_1576_);
lean_ctor_set(v___x_1589_, 2, v_v_1578_);
lean_ctor_set(v___x_1589_, 1, v_k_1577_);
lean_ctor_set(v___x_1589_, 0, v___x_1635_);
v___x_1637_ = v___x_1589_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_k_1577_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_v_1578_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_tree_1576_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_l_1568_);
v___x_1637_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 4, v_r_1569_);
lean_ctor_set(v___x_1573_, 3, v___x_1637_);
lean_ctor_set(v___x_1573_, 2, v_v_1567_);
lean_ctor_set(v___x_1573_, 1, v_k_1566_);
lean_ctor_set(v___x_1573_, 0, v___x_1634_);
v___x_1639_ = v___x_1573_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_r_1569_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
}
else
{
lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1701_; 
lean_inc(v_r_1569_);
lean_inc(v_v_1567_);
lean_inc(v_k_1566_);
lean_inc(v_size_1565_);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_r_1381_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; lean_object* v_unused_1703_; lean_object* v_unused_1704_; lean_object* v_unused_1705_; lean_object* v_unused_1706_; 
v_unused_1702_ = lean_ctor_get(v_r_1381_, 4);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_r_1381_, 3);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v_r_1381_, 2);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_r_1381_, 1);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_r_1381_, 0);
lean_dec(v_unused_1706_);
v___x_1649_ = v_r_1381_;
v_isShared_1650_ = v_isSharedCheck_1701_;
goto v_resetjp_1648_;
}
else
{
lean_dec(v_r_1381_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1701_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
if (lean_obj_tag(v_l_1568_) == 0)
{
if (lean_obj_tag(v_r_1569_) == 0)
{
lean_object* v_k_1651_; lean_object* v_v_1652_; lean_object* v_size_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v_k_1651_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_k_1651_);
v_v_1652_ = lean_ctor_get(v___x_1575_, 1);
lean_inc(v_v_1652_);
lean_dec_ref(v___x_1575_);
v_size_1653_ = lean_ctor_get(v_l_1568_, 0);
v___x_1654_ = lean_nat_add(v___x_1570_, v_size_1565_);
lean_dec(v_size_1565_);
v___x_1655_ = lean_nat_add(v___x_1570_, v_size_1653_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 4, v_l_1568_);
lean_ctor_set(v___x_1649_, 3, v_tree_1576_);
lean_ctor_set(v___x_1649_, 2, v_v_1652_);
lean_ctor_set(v___x_1649_, 1, v_k_1651_);
lean_ctor_set(v___x_1649_, 0, v___x_1655_);
v___x_1657_ = v___x_1649_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_k_1651_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_v_1652_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_tree_1576_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_l_1568_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 4, v_r_1569_);
lean_ctor_set(v___x_1573_, 3, v___x_1657_);
lean_ctor_set(v___x_1573_, 2, v_v_1567_);
lean_ctor_set(v___x_1573_, 1, v_k_1566_);
lean_ctor_set(v___x_1573_, 0, v___x_1654_);
v___x_1659_ = v___x_1573_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_r_1569_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
lean_object* v_k_1662_; lean_object* v_v_1663_; lean_object* v_k_1664_; lean_object* v_v_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_size_1565_);
v_k_1662_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_k_1662_);
v_v_1663_ = lean_ctor_get(v___x_1575_, 1);
lean_inc(v_v_1663_);
lean_dec_ref(v___x_1575_);
v_k_1664_ = lean_ctor_get(v_l_1568_, 1);
v_v_1665_ = lean_ctor_get(v_l_1568_, 2);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_l_1568_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; lean_object* v_unused_1681_; lean_object* v_unused_1682_; 
v_unused_1680_ = lean_ctor_get(v_l_1568_, 4);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_l_1568_, 3);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_l_1568_, 0);
lean_dec(v_unused_1682_);
v___x_1667_ = v_l_1568_;
v_isShared_1668_ = v_isSharedCheck_1679_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_v_1665_);
lean_inc(v_k_1664_);
lean_dec(v_l_1568_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1679_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = lean_unsigned_to_nat(3u);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 4, v_r_1569_);
lean_ctor_set(v___x_1667_, 3, v_r_1569_);
lean_ctor_set(v___x_1667_, 2, v_v_1663_);
lean_ctor_set(v___x_1667_, 1, v_k_1662_);
lean_ctor_set(v___x_1667_, 0, v___x_1570_);
v___x_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_k_1662_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v_v_1663_);
lean_ctor_set(v_reuseFailAlloc_1678_, 3, v_r_1569_);
lean_ctor_set(v_reuseFailAlloc_1678_, 4, v_r_1569_);
v___x_1671_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1673_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 3, v_r_1569_);
lean_ctor_set(v___x_1649_, 0, v___x_1570_);
v___x_1673_ = v___x_1649_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v_r_1569_);
lean_ctor_set(v_reuseFailAlloc_1677_, 4, v_r_1569_);
v___x_1673_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1675_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 4, v___x_1673_);
lean_ctor_set(v___x_1573_, 3, v___x_1671_);
lean_ctor_set(v___x_1573_, 2, v_v_1665_);
lean_ctor_set(v___x_1573_, 1, v_k_1664_);
lean_ctor_set(v___x_1573_, 0, v___x_1669_);
v___x_1675_ = v___x_1573_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_k_1664_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_v_1665_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1676_, 4, v___x_1673_);
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
}
}
else
{
if (lean_obj_tag(v_r_1569_) == 0)
{
lean_object* v_k_1683_; lean_object* v_v_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
lean_dec(v_size_1565_);
v_k_1683_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_k_1683_);
v_v_1684_ = lean_ctor_get(v___x_1575_, 1);
lean_inc(v_v_1684_);
lean_dec_ref(v___x_1575_);
v___x_1685_ = lean_unsigned_to_nat(3u);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 4, v_l_1568_);
lean_ctor_set(v___x_1649_, 2, v_v_1684_);
lean_ctor_set(v___x_1649_, 1, v_k_1683_);
lean_ctor_set(v___x_1649_, 0, v___x_1570_);
v___x_1687_ = v___x_1649_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_k_1683_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_v_1684_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_l_1568_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v_l_1568_);
v___x_1687_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 4, v_r_1569_);
lean_ctor_set(v___x_1573_, 3, v___x_1687_);
lean_ctor_set(v___x_1573_, 2, v_v_1567_);
lean_ctor_set(v___x_1573_, 1, v_k_1566_);
lean_ctor_set(v___x_1573_, 0, v___x_1685_);
v___x_1689_ = v___x_1573_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_r_1569_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
else
{
lean_object* v_k_1692_; lean_object* v_v_1693_; lean_object* v___x_1695_; 
v_k_1692_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_k_1692_);
v_v_1693_ = lean_ctor_get(v___x_1575_, 1);
lean_inc(v_v_1693_);
lean_dec_ref(v___x_1575_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 3, v_r_1569_);
v___x_1695_ = v___x_1649_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_size_1565_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_r_1569_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v_r_1569_);
v___x_1695_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(2u);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 4, v___x_1695_);
lean_ctor_set(v___x_1573_, 3, v_r_1569_);
lean_ctor_set(v___x_1573_, 2, v_v_1693_);
lean_ctor_set(v___x_1573_, 1, v_k_1692_);
lean_ctor_set(v___x_1573_, 0, v___x_1696_);
v___x_1698_ = v___x_1573_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_k_1692_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_v_1693_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_r_1569_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v___x_1695_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1865_; 
lean_inc(v_r_1569_);
lean_inc(v_v_1567_);
lean_inc(v_k_1566_);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_r_1381_);
if (v_isSharedCheck_1865_ == 0)
{
lean_object* v_unused_1866_; lean_object* v_unused_1867_; lean_object* v_unused_1868_; lean_object* v_unused_1869_; lean_object* v_unused_1870_; 
v_unused_1866_ = lean_ctor_get(v_r_1381_, 4);
lean_dec(v_unused_1866_);
v_unused_1867_ = lean_ctor_get(v_r_1381_, 3);
lean_dec(v_unused_1867_);
v_unused_1868_ = lean_ctor_get(v_r_1381_, 2);
lean_dec(v_unused_1868_);
v_unused_1869_ = lean_ctor_get(v_r_1381_, 1);
lean_dec(v_unused_1869_);
v_unused_1870_ = lean_ctor_get(v_r_1381_, 0);
lean_dec(v_unused_1870_);
v___x_1714_ = v_r_1381_;
v_isShared_1715_ = v_isSharedCheck_1865_;
goto v_resetjp_1713_;
}
else
{
lean_dec(v_r_1381_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1865_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v_tree_1717_; 
v___x_1716_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1566_, v_v_1567_, v_l_1568_, v_r_1569_);
v_tree_1717_ = lean_ctor_get(v___x_1716_, 2);
lean_inc(v_tree_1717_);
if (lean_obj_tag(v_tree_1717_) == 0)
{
lean_object* v_k_1718_; lean_object* v_v_1719_; lean_object* v_size_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v_k_1718_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_k_1718_);
v_v_1719_ = lean_ctor_get(v___x_1716_, 1);
lean_inc(v_v_1719_);
lean_dec_ref(v___x_1716_);
v_size_1720_ = lean_ctor_get(v_tree_1717_, 0);
v___x_1721_ = lean_unsigned_to_nat(3u);
v___x_1722_ = lean_nat_mul(v___x_1721_, v_size_1720_);
v___x_1723_ = lean_nat_dec_lt(v___x_1722_, v_size_1560_);
lean_dec(v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
lean_dec(v_r_1564_);
v___x_1724_ = lean_nat_add(v___x_1570_, v_size_1560_);
v___x_1725_ = lean_nat_add(v___x_1724_, v_size_1720_);
lean_dec(v___x_1724_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 4, v_tree_1717_);
lean_ctor_set(v___x_1714_, 3, v_l_1380_);
lean_ctor_set(v___x_1714_, 2, v_v_1719_);
lean_ctor_set(v___x_1714_, 1, v_k_1718_);
lean_ctor_set(v___x_1714_, 0, v___x_1725_);
v___x_1727_ = v___x_1714_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_k_1718_);
lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_v_1719_);
lean_ctor_set(v_reuseFailAlloc_1728_, 3, v_l_1380_);
lean_ctor_set(v_reuseFailAlloc_1728_, 4, v_tree_1717_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
else
{
lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1794_; 
lean_inc(v_l_1563_);
lean_inc(v_v_1562_);
lean_inc(v_k_1561_);
lean_inc(v_size_1560_);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_l_1380_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; lean_object* v_unused_1796_; lean_object* v_unused_1797_; lean_object* v_unused_1798_; lean_object* v_unused_1799_; 
v_unused_1795_ = lean_ctor_get(v_l_1380_, 4);
lean_dec(v_unused_1795_);
v_unused_1796_ = lean_ctor_get(v_l_1380_, 3);
lean_dec(v_unused_1796_);
v_unused_1797_ = lean_ctor_get(v_l_1380_, 2);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_l_1380_, 1);
lean_dec(v_unused_1798_);
v_unused_1799_ = lean_ctor_get(v_l_1380_, 0);
lean_dec(v_unused_1799_);
v___x_1730_ = v_l_1380_;
v_isShared_1731_ = v_isSharedCheck_1794_;
goto v_resetjp_1729_;
}
else
{
lean_dec(v_l_1380_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1794_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_size_1732_; lean_object* v_size_1733_; lean_object* v_k_1734_; lean_object* v_v_1735_; lean_object* v_l_1736_; lean_object* v_r_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v_size_1732_ = lean_ctor_get(v_l_1563_, 0);
v_size_1733_ = lean_ctor_get(v_r_1564_, 0);
v_k_1734_ = lean_ctor_get(v_r_1564_, 1);
v_v_1735_ = lean_ctor_get(v_r_1564_, 2);
v_l_1736_ = lean_ctor_get(v_r_1564_, 3);
v_r_1737_ = lean_ctor_get(v_r_1564_, 4);
v___x_1738_ = lean_unsigned_to_nat(2u);
v___x_1739_ = lean_nat_mul(v___x_1738_, v_size_1732_);
v___x_1740_ = lean_nat_dec_lt(v_size_1733_, v___x_1739_);
lean_dec(v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1778_; 
lean_inc(v_r_1737_);
lean_inc(v_l_1736_);
lean_inc(v_v_1735_);
lean_inc(v_k_1734_);
lean_del_object(v___x_1730_);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_r_1564_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; lean_object* v_unused_1780_; lean_object* v_unused_1781_; lean_object* v_unused_1782_; lean_object* v_unused_1783_; 
v_unused_1779_ = lean_ctor_get(v_r_1564_, 4);
lean_dec(v_unused_1779_);
v_unused_1780_ = lean_ctor_get(v_r_1564_, 3);
lean_dec(v_unused_1780_);
v_unused_1781_ = lean_ctor_get(v_r_1564_, 2);
lean_dec(v_unused_1781_);
v_unused_1782_ = lean_ctor_get(v_r_1564_, 1);
lean_dec(v_unused_1782_);
v_unused_1783_ = lean_ctor_get(v_r_1564_, 0);
lean_dec(v_unused_1783_);
v___x_1742_ = v_r_1564_;
v_isShared_1743_ = v_isSharedCheck_1778_;
goto v_resetjp_1741_;
}
else
{
lean_dec(v_r_1564_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1778_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___x_1766_; lean_object* v___y_1768_; 
v___x_1744_ = lean_nat_add(v___x_1570_, v_size_1560_);
lean_dec(v_size_1560_);
v___x_1745_ = lean_nat_add(v___x_1744_, v_size_1720_);
lean_dec(v___x_1744_);
v___x_1766_ = lean_nat_add(v___x_1570_, v_size_1732_);
if (lean_obj_tag(v_l_1736_) == 0)
{
lean_object* v_size_1776_; 
v_size_1776_ = lean_ctor_get(v_l_1736_, 0);
lean_inc(v_size_1776_);
v___y_1768_ = v_size_1776_;
goto v___jp_1767_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_unsigned_to_nat(0u);
v___y_1768_ = v___x_1777_;
goto v___jp_1767_;
}
v___jp_1746_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = lean_nat_add(v___y_1747_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec(v___y_1747_);
lean_inc_ref(v_tree_1717_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 4, v_tree_1717_);
lean_ctor_set(v___x_1742_, 3, v_r_1737_);
lean_ctor_set(v___x_1742_, 2, v_v_1719_);
lean_ctor_set(v___x_1742_, 1, v_k_1718_);
lean_ctor_set(v___x_1742_, 0, v___x_1750_);
v___x_1752_ = v___x_1742_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_k_1718_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_v_1719_);
lean_ctor_set(v_reuseFailAlloc_1765_, 3, v_r_1737_);
lean_ctor_set(v_reuseFailAlloc_1765_, 4, v_tree_1717_);
v___x_1752_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
v_isSharedCheck_1759_ = !lean_is_exclusive(v_tree_1717_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; lean_object* v_unused_1761_; lean_object* v_unused_1762_; lean_object* v_unused_1763_; lean_object* v_unused_1764_; 
v_unused_1760_ = lean_ctor_get(v_tree_1717_, 4);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v_tree_1717_, 3);
lean_dec(v_unused_1761_);
v_unused_1762_ = lean_ctor_get(v_tree_1717_, 2);
lean_dec(v_unused_1762_);
v_unused_1763_ = lean_ctor_get(v_tree_1717_, 1);
lean_dec(v_unused_1763_);
v_unused_1764_ = lean_ctor_get(v_tree_1717_, 0);
lean_dec(v_unused_1764_);
v___x_1754_ = v_tree_1717_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_dec(v_tree_1717_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 4, v___x_1752_);
lean_ctor_set(v___x_1754_, 3, v___y_1748_);
lean_ctor_set(v___x_1754_, 2, v_v_1735_);
lean_ctor_set(v___x_1754_, 1, v_k_1734_);
lean_ctor_set(v___x_1754_, 0, v___x_1745_);
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1745_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_k_1734_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_v_1735_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v___y_1748_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v___x_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
v___jp_1767_:
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1769_ = lean_nat_add(v___x_1766_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec(v___x_1766_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 4, v_l_1736_);
lean_ctor_set(v___x_1714_, 3, v_l_1563_);
lean_ctor_set(v___x_1714_, 2, v_v_1562_);
lean_ctor_set(v___x_1714_, 1, v_k_1561_);
lean_ctor_set(v___x_1714_, 0, v___x_1769_);
v___x_1771_ = v___x_1714_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_k_1561_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_v_1562_);
lean_ctor_set(v_reuseFailAlloc_1775_, 3, v_l_1563_);
lean_ctor_set(v_reuseFailAlloc_1775_, 4, v_l_1736_);
v___x_1771_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_nat_add(v___x_1570_, v_size_1720_);
if (lean_obj_tag(v_r_1737_) == 0)
{
lean_object* v_size_1773_; 
v_size_1773_ = lean_ctor_get(v_r_1737_, 0);
lean_inc(v_size_1773_);
v___y_1747_ = v___x_1772_;
v___y_1748_ = v___x_1771_;
v___y_1749_ = v_size_1773_;
goto v___jp_1746_;
}
else
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_unsigned_to_nat(0u);
v___y_1747_ = v___x_1772_;
v___y_1748_ = v___x_1771_;
v___y_1749_ = v___x_1774_;
goto v___jp_1746_;
}
}
}
}
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1784_ = lean_nat_add(v___x_1570_, v_size_1560_);
lean_dec(v_size_1560_);
v___x_1785_ = lean_nat_add(v___x_1784_, v_size_1720_);
lean_dec(v___x_1784_);
v___x_1786_ = lean_nat_add(v___x_1570_, v_size_1720_);
v___x_1787_ = lean_nat_add(v___x_1786_, v_size_1733_);
lean_dec(v___x_1786_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 4, v_tree_1717_);
lean_ctor_set(v___x_1714_, 3, v_r_1564_);
lean_ctor_set(v___x_1714_, 2, v_v_1719_);
lean_ctor_set(v___x_1714_, 1, v_k_1718_);
lean_ctor_set(v___x_1714_, 0, v___x_1787_);
v___x_1789_ = v___x_1714_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1787_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_k_1718_);
lean_ctor_set(v_reuseFailAlloc_1793_, 2, v_v_1719_);
lean_ctor_set(v_reuseFailAlloc_1793_, 3, v_r_1564_);
lean_ctor_set(v_reuseFailAlloc_1793_, 4, v_tree_1717_);
v___x_1789_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1791_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 4, v___x_1789_);
lean_ctor_set(v___x_1730_, 0, v___x_1785_);
v___x_1791_ = v___x_1730_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_k_1561_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_v_1562_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_l_1563_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1563_) == 0)
{
lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1823_; 
lean_inc_ref(v_l_1563_);
lean_inc(v_v_1562_);
lean_inc(v_k_1561_);
lean_inc(v_size_1560_);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_l_1380_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; lean_object* v_unused_1825_; lean_object* v_unused_1826_; lean_object* v_unused_1827_; lean_object* v_unused_1828_; 
v_unused_1824_ = lean_ctor_get(v_l_1380_, 4);
lean_dec(v_unused_1824_);
v_unused_1825_ = lean_ctor_get(v_l_1380_, 3);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_l_1380_, 2);
lean_dec(v_unused_1826_);
v_unused_1827_ = lean_ctor_get(v_l_1380_, 1);
lean_dec(v_unused_1827_);
v_unused_1828_ = lean_ctor_get(v_l_1380_, 0);
lean_dec(v_unused_1828_);
v___x_1801_ = v_l_1380_;
v_isShared_1802_ = v_isSharedCheck_1823_;
goto v_resetjp_1800_;
}
else
{
lean_dec(v_l_1380_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1823_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
if (lean_obj_tag(v_r_1564_) == 0)
{
lean_object* v_k_1803_; lean_object* v_v_1804_; lean_object* v_size_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v_k_1803_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_k_1803_);
v_v_1804_ = lean_ctor_get(v___x_1716_, 1);
lean_inc(v_v_1804_);
lean_dec_ref(v___x_1716_);
v_size_1805_ = lean_ctor_get(v_r_1564_, 0);
v___x_1806_ = lean_nat_add(v___x_1570_, v_size_1560_);
lean_dec(v_size_1560_);
v___x_1807_ = lean_nat_add(v___x_1570_, v_size_1805_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 4, v_tree_1717_);
lean_ctor_set(v___x_1714_, 3, v_r_1564_);
lean_ctor_set(v___x_1714_, 2, v_v_1804_);
lean_ctor_set(v___x_1714_, 1, v_k_1803_);
lean_ctor_set(v___x_1714_, 0, v___x_1807_);
v___x_1809_ = v___x_1714_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_k_1803_);
lean_ctor_set(v_reuseFailAlloc_1813_, 2, v_v_1804_);
lean_ctor_set(v_reuseFailAlloc_1813_, 3, v_r_1564_);
lean_ctor_set(v_reuseFailAlloc_1813_, 4, v_tree_1717_);
v___x_1809_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1811_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 4, v___x_1809_);
lean_ctor_set(v___x_1801_, 0, v___x_1806_);
v___x_1811_ = v___x_1801_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1806_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_k_1561_);
lean_ctor_set(v_reuseFailAlloc_1812_, 2, v_v_1562_);
lean_ctor_set(v_reuseFailAlloc_1812_, 3, v_l_1563_);
lean_ctor_set(v_reuseFailAlloc_1812_, 4, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
else
{
lean_object* v_k_1814_; lean_object* v_v_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
lean_dec(v_size_1560_);
v_k_1814_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_k_1814_);
v_v_1815_ = lean_ctor_get(v___x_1716_, 1);
lean_inc(v_v_1815_);
lean_dec_ref(v___x_1716_);
v___x_1816_ = lean_unsigned_to_nat(3u);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 4, v_r_1564_);
lean_ctor_set(v___x_1714_, 3, v_r_1564_);
lean_ctor_set(v___x_1714_, 2, v_v_1815_);
lean_ctor_set(v___x_1714_, 1, v_k_1814_);
lean_ctor_set(v___x_1714_, 0, v___x_1570_);
v___x_1818_ = v___x_1714_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_1822_, 3, v_r_1564_);
lean_ctor_set(v_reuseFailAlloc_1822_, 4, v_r_1564_);
v___x_1818_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1820_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 4, v___x_1818_);
lean_ctor_set(v___x_1801_, 0, v___x_1816_);
v___x_1820_ = v___x_1801_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_k_1561_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_v_1562_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v_l_1563_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1564_) == 0)
{
lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1853_; 
lean_inc(v_l_1563_);
lean_inc(v_v_1562_);
lean_inc(v_k_1561_);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_l_1380_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; 
v_unused_1854_ = lean_ctor_get(v_l_1380_, 4);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_l_1380_, 3);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_l_1380_, 2);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_l_1380_, 1);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_l_1380_, 0);
lean_dec(v_unused_1858_);
v___x_1830_ = v_l_1380_;
v_isShared_1831_ = v_isSharedCheck_1853_;
goto v_resetjp_1829_;
}
else
{
lean_dec(v_l_1380_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1853_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v_k_1832_; lean_object* v_v_1833_; lean_object* v_k_1834_; lean_object* v_v_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1849_; 
v_k_1832_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_k_1832_);
v_v_1833_ = lean_ctor_get(v___x_1716_, 1);
lean_inc(v_v_1833_);
lean_dec_ref(v___x_1716_);
v_k_1834_ = lean_ctor_get(v_r_1564_, 1);
v_v_1835_ = lean_ctor_get(v_r_1564_, 2);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_r_1564_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; lean_object* v_unused_1851_; lean_object* v_unused_1852_; 
v_unused_1850_ = lean_ctor_get(v_r_1564_, 4);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_r_1564_, 3);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_r_1564_, 0);
lean_dec(v_unused_1852_);
v___x_1837_ = v_r_1564_;
v_isShared_1838_ = v_isSharedCheck_1849_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_v_1835_);
lean_inc(v_k_1834_);
lean_dec(v_r_1564_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1849_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = lean_unsigned_to_nat(3u);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 4, v_l_1563_);
lean_ctor_set(v___x_1837_, 3, v_l_1563_);
lean_ctor_set(v___x_1837_, 2, v_v_1562_);
lean_ctor_set(v___x_1837_, 1, v_k_1561_);
lean_ctor_set(v___x_1837_, 0, v___x_1570_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_k_1561_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_v_1562_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_l_1563_);
lean_ctor_set(v_reuseFailAlloc_1848_, 4, v_l_1563_);
v___x_1841_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 4, v_l_1563_);
lean_ctor_set(v___x_1714_, 3, v_l_1563_);
lean_ctor_set(v___x_1714_, 2, v_v_1833_);
lean_ctor_set(v___x_1714_, 1, v_k_1832_);
lean_ctor_set(v___x_1714_, 0, v___x_1570_);
v___x_1843_ = v___x_1714_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_k_1832_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_v_1833_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_l_1563_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v_l_1563_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 4, v___x_1843_);
lean_ctor_set(v___x_1830_, 3, v___x_1841_);
lean_ctor_set(v___x_1830_, 2, v_v_1835_);
lean_ctor_set(v___x_1830_, 1, v_k_1834_);
lean_ctor_set(v___x_1830_, 0, v___x_1839_);
v___x_1845_ = v___x_1830_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_k_1834_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_v_1835_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
}
else
{
lean_object* v_k_1859_; lean_object* v_v_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v_k_1859_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_k_1859_);
v_v_1860_ = lean_ctor_get(v___x_1716_, 1);
lean_inc(v_v_1860_);
lean_dec_ref(v___x_1716_);
v___x_1861_ = lean_unsigned_to_nat(2u);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 4, v_r_1564_);
lean_ctor_set(v___x_1714_, 3, v_l_1380_);
lean_ctor_set(v___x_1714_, 2, v_v_1860_);
lean_ctor_set(v___x_1714_, 1, v_k_1859_);
lean_ctor_set(v___x_1714_, 0, v___x_1861_);
v___x_1863_ = v___x_1714_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_k_1859_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_v_1860_);
lean_ctor_set(v_reuseFailAlloc_1864_, 3, v_l_1380_);
lean_ctor_set(v_reuseFailAlloc_1864_, 4, v_r_1564_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
}
else
{
return v_l_1380_;
}
}
else
{
return v_r_1381_;
}
}
default: 
{
lean_object* v_impl_1871_; lean_object* v___x_1872_; 
v_impl_1871_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1376_, v_r_1381_);
v___x_1872_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1871_) == 0)
{
if (lean_obj_tag(v_l_1380_) == 0)
{
lean_object* v_size_1873_; lean_object* v_size_1874_; lean_object* v_k_1875_; lean_object* v_v_1876_; lean_object* v_l_1877_; lean_object* v_r_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v_size_1873_ = lean_ctor_get(v_impl_1871_, 0);
lean_inc(v_size_1873_);
v_size_1874_ = lean_ctor_get(v_l_1380_, 0);
v_k_1875_ = lean_ctor_get(v_l_1380_, 1);
v_v_1876_ = lean_ctor_get(v_l_1380_, 2);
v_l_1877_ = lean_ctor_get(v_l_1380_, 3);
v_r_1878_ = lean_ctor_get(v_l_1380_, 4);
lean_inc(v_r_1878_);
v___x_1879_ = lean_unsigned_to_nat(3u);
v___x_1880_ = lean_nat_mul(v___x_1879_, v_size_1873_);
v___x_1881_ = lean_nat_dec_lt(v___x_1880_, v_size_1874_);
lean_dec(v___x_1880_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
lean_dec(v_r_1878_);
v___x_1882_ = lean_nat_add(v___x_1872_, v_size_1874_);
v___x_1883_ = lean_nat_add(v___x_1882_, v_size_1873_);
lean_dec(v_size_1873_);
lean_dec(v___x_1882_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_impl_1871_);
lean_ctor_set(v___x_1383_, 0, v___x_1883_);
v___x_1885_ = v___x_1383_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1886_, 3, v_l_1380_);
lean_ctor_set(v_reuseFailAlloc_1886_, 4, v_impl_1871_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
else
{
lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1952_; 
lean_inc(v_l_1877_);
lean_inc(v_v_1876_);
lean_inc(v_k_1875_);
lean_inc(v_size_1874_);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_l_1380_);
if (v_isSharedCheck_1952_ == 0)
{
lean_object* v_unused_1953_; lean_object* v_unused_1954_; lean_object* v_unused_1955_; lean_object* v_unused_1956_; lean_object* v_unused_1957_; 
v_unused_1953_ = lean_ctor_get(v_l_1380_, 4);
lean_dec(v_unused_1953_);
v_unused_1954_ = lean_ctor_get(v_l_1380_, 3);
lean_dec(v_unused_1954_);
v_unused_1955_ = lean_ctor_get(v_l_1380_, 2);
lean_dec(v_unused_1955_);
v_unused_1956_ = lean_ctor_get(v_l_1380_, 1);
lean_dec(v_unused_1956_);
v_unused_1957_ = lean_ctor_get(v_l_1380_, 0);
lean_dec(v_unused_1957_);
v___x_1888_ = v_l_1380_;
v_isShared_1889_ = v_isSharedCheck_1952_;
goto v_resetjp_1887_;
}
else
{
lean_dec(v_l_1380_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1952_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_size_1890_; lean_object* v_size_1891_; lean_object* v_k_1892_; lean_object* v_v_1893_; lean_object* v_l_1894_; lean_object* v_r_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v_size_1890_ = lean_ctor_get(v_l_1877_, 0);
v_size_1891_ = lean_ctor_get(v_r_1878_, 0);
v_k_1892_ = lean_ctor_get(v_r_1878_, 1);
v_v_1893_ = lean_ctor_get(v_r_1878_, 2);
v_l_1894_ = lean_ctor_get(v_r_1878_, 3);
v_r_1895_ = lean_ctor_get(v_r_1878_, 4);
v___x_1896_ = lean_unsigned_to_nat(2u);
v___x_1897_ = lean_nat_mul(v___x_1896_, v_size_1890_);
v___x_1898_ = lean_nat_dec_lt(v_size_1891_, v___x_1897_);
lean_dec(v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1927_; 
lean_inc(v_r_1895_);
lean_inc(v_l_1894_);
lean_inc(v_v_1893_);
lean_inc(v_k_1892_);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_r_1878_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; lean_object* v_unused_1929_; lean_object* v_unused_1930_; lean_object* v_unused_1931_; lean_object* v_unused_1932_; 
v_unused_1928_ = lean_ctor_get(v_r_1878_, 4);
lean_dec(v_unused_1928_);
v_unused_1929_ = lean_ctor_get(v_r_1878_, 3);
lean_dec(v_unused_1929_);
v_unused_1930_ = lean_ctor_get(v_r_1878_, 2);
lean_dec(v_unused_1930_);
v_unused_1931_ = lean_ctor_get(v_r_1878_, 1);
lean_dec(v_unused_1931_);
v_unused_1932_ = lean_ctor_get(v_r_1878_, 0);
lean_dec(v_unused_1932_);
v___x_1900_ = v_r_1878_;
v_isShared_1901_ = v_isSharedCheck_1927_;
goto v_resetjp_1899_;
}
else
{
lean_dec(v_r_1878_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1927_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___x_1915_; lean_object* v___y_1917_; 
v___x_1902_ = lean_nat_add(v___x_1872_, v_size_1874_);
lean_dec(v_size_1874_);
v___x_1903_ = lean_nat_add(v___x_1902_, v_size_1873_);
lean_dec(v___x_1902_);
v___x_1915_ = lean_nat_add(v___x_1872_, v_size_1890_);
if (lean_obj_tag(v_l_1894_) == 0)
{
lean_object* v_size_1925_; 
v_size_1925_ = lean_ctor_get(v_l_1894_, 0);
lean_inc(v_size_1925_);
v___y_1917_ = v_size_1925_;
goto v___jp_1916_;
}
else
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_unsigned_to_nat(0u);
v___y_1917_ = v___x_1926_;
goto v___jp_1916_;
}
v___jp_1904_:
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1908_ = lean_nat_add(v___y_1905_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec(v___y_1905_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 4, v_impl_1871_);
lean_ctor_set(v___x_1900_, 3, v_r_1895_);
lean_ctor_set(v___x_1900_, 2, v_v_1379_);
lean_ctor_set(v___x_1900_, 1, v_k_1378_);
lean_ctor_set(v___x_1900_, 0, v___x_1908_);
v___x_1910_ = v___x_1900_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_r_1895_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_impl_1871_);
v___x_1910_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1912_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 4, v___x_1910_);
lean_ctor_set(v___x_1888_, 3, v___y_1906_);
lean_ctor_set(v___x_1888_, 2, v_v_1893_);
lean_ctor_set(v___x_1888_, 1, v_k_1892_);
lean_ctor_set(v___x_1888_, 0, v___x_1903_);
v___x_1912_ = v___x_1888_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_k_1892_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_v_1893_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v___y_1906_);
lean_ctor_set(v_reuseFailAlloc_1913_, 4, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
v___jp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1918_ = lean_nat_add(v___x_1915_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec(v___x_1915_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_l_1894_);
lean_ctor_set(v___x_1383_, 3, v_l_1877_);
lean_ctor_set(v___x_1383_, 2, v_v_1876_);
lean_ctor_set(v___x_1383_, 1, v_k_1875_);
lean_ctor_set(v___x_1383_, 0, v___x_1918_);
v___x_1920_ = v___x_1383_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_k_1875_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_v_1876_);
lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_l_1877_);
lean_ctor_set(v_reuseFailAlloc_1924_, 4, v_l_1894_);
v___x_1920_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_nat_add(v___x_1872_, v_size_1873_);
lean_dec(v_size_1873_);
if (lean_obj_tag(v_r_1895_) == 0)
{
lean_object* v_size_1922_; 
v_size_1922_ = lean_ctor_get(v_r_1895_, 0);
lean_inc(v_size_1922_);
v___y_1905_ = v___x_1921_;
v___y_1906_ = v___x_1920_;
v___y_1907_ = v_size_1922_;
goto v___jp_1904_;
}
else
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_unsigned_to_nat(0u);
v___y_1905_ = v___x_1921_;
v___y_1906_ = v___x_1920_;
v___y_1907_ = v___x_1923_;
goto v___jp_1904_;
}
}
}
}
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
lean_del_object(v___x_1383_);
v___x_1933_ = lean_nat_add(v___x_1872_, v_size_1874_);
lean_dec(v_size_1874_);
v___x_1934_ = lean_nat_add(v___x_1933_, v_size_1873_);
lean_dec(v___x_1933_);
v___x_1935_ = lean_nat_add(v___x_1872_, v_size_1873_);
lean_dec(v_size_1873_);
v___x_1936_ = lean_nat_add(v___x_1935_, v_size_1891_);
lean_dec(v___x_1935_);
lean_inc_ref(v_impl_1871_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 4, v_impl_1871_);
lean_ctor_set(v___x_1888_, 3, v_r_1878_);
lean_ctor_set(v___x_1888_, 2, v_v_1379_);
lean_ctor_set(v___x_1888_, 1, v_k_1378_);
lean_ctor_set(v___x_1888_, 0, v___x_1936_);
v___x_1938_ = v___x_1888_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_r_1878_);
lean_ctor_set(v_reuseFailAlloc_1951_, 4, v_impl_1871_);
v___x_1938_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_isSharedCheck_1945_ = !lean_is_exclusive(v_impl_1871_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; lean_object* v_unused_1947_; lean_object* v_unused_1948_; lean_object* v_unused_1949_; lean_object* v_unused_1950_; 
v_unused_1946_ = lean_ctor_get(v_impl_1871_, 4);
lean_dec(v_unused_1946_);
v_unused_1947_ = lean_ctor_get(v_impl_1871_, 3);
lean_dec(v_unused_1947_);
v_unused_1948_ = lean_ctor_get(v_impl_1871_, 2);
lean_dec(v_unused_1948_);
v_unused_1949_ = lean_ctor_get(v_impl_1871_, 1);
lean_dec(v_unused_1949_);
v_unused_1950_ = lean_ctor_get(v_impl_1871_, 0);
lean_dec(v_unused_1950_);
v___x_1940_ = v_impl_1871_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_dec(v_impl_1871_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 4, v___x_1938_);
lean_ctor_set(v___x_1940_, 3, v_l_1877_);
lean_ctor_set(v___x_1940_, 2, v_v_1876_);
lean_ctor_set(v___x_1940_, 1, v_k_1875_);
lean_ctor_set(v___x_1940_, 0, v___x_1934_);
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_k_1875_);
lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_v_1876_);
lean_ctor_set(v_reuseFailAlloc_1944_, 3, v_l_1877_);
lean_ctor_set(v_reuseFailAlloc_1944_, 4, v___x_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v_size_1958_ = lean_ctor_get(v_impl_1871_, 0);
lean_inc(v_size_1958_);
v___x_1959_ = lean_nat_add(v___x_1872_, v_size_1958_);
lean_dec(v_size_1958_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_impl_1871_);
lean_ctor_set(v___x_1383_, 0, v___x_1959_);
v___x_1961_ = v___x_1383_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1962_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1962_, 3, v_l_1380_);
lean_ctor_set(v_reuseFailAlloc_1962_, 4, v_impl_1871_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
else
{
if (lean_obj_tag(v_l_1380_) == 0)
{
lean_object* v_l_1963_; 
v_l_1963_ = lean_ctor_get(v_l_1380_, 3);
if (lean_obj_tag(v_l_1963_) == 0)
{
lean_object* v_r_1964_; 
lean_inc_ref(v_l_1963_);
v_r_1964_ = lean_ctor_get(v_l_1380_, 4);
lean_inc(v_r_1964_);
if (lean_obj_tag(v_r_1964_) == 0)
{
lean_object* v_size_1965_; lean_object* v_k_1966_; lean_object* v_v_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1980_; 
v_size_1965_ = lean_ctor_get(v_l_1380_, 0);
v_k_1966_ = lean_ctor_get(v_l_1380_, 1);
v_v_1967_ = lean_ctor_get(v_l_1380_, 2);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_l_1380_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; lean_object* v_unused_1982_; 
v_unused_1981_ = lean_ctor_get(v_l_1380_, 4);
lean_dec(v_unused_1981_);
v_unused_1982_ = lean_ctor_get(v_l_1380_, 3);
lean_dec(v_unused_1982_);
v___x_1969_ = v_l_1380_;
v_isShared_1970_ = v_isSharedCheck_1980_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_v_1967_);
lean_inc(v_k_1966_);
lean_inc(v_size_1965_);
lean_dec(v_l_1380_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1980_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v_size_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
v_size_1971_ = lean_ctor_get(v_r_1964_, 0);
v___x_1972_ = lean_nat_add(v___x_1872_, v_size_1965_);
lean_dec(v_size_1965_);
v___x_1973_ = lean_nat_add(v___x_1872_, v_size_1971_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 4, v_impl_1871_);
lean_ctor_set(v___x_1969_, 3, v_r_1964_);
lean_ctor_set(v___x_1969_, 2, v_v_1379_);
lean_ctor_set(v___x_1969_, 1, v_k_1378_);
lean_ctor_set(v___x_1969_, 0, v___x_1973_);
v___x_1975_ = v___x_1969_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1979_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1979_, 3, v_r_1964_);
lean_ctor_set(v_reuseFailAlloc_1979_, 4, v_impl_1871_);
v___x_1975_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1977_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v___x_1975_);
lean_ctor_set(v___x_1383_, 3, v_l_1963_);
lean_ctor_set(v___x_1383_, 2, v_v_1967_);
lean_ctor_set(v___x_1383_, 1, v_k_1966_);
lean_ctor_set(v___x_1383_, 0, v___x_1972_);
v___x_1977_ = v___x_1383_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_1978_, 3, v_l_1963_);
lean_ctor_set(v_reuseFailAlloc_1978_, 4, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_k_1983_; lean_object* v_v_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1995_; 
v_k_1983_ = lean_ctor_get(v_l_1380_, 1);
v_v_1984_ = lean_ctor_get(v_l_1380_, 2);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_l_1380_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; lean_object* v_unused_1997_; lean_object* v_unused_1998_; 
v_unused_1996_ = lean_ctor_get(v_l_1380_, 4);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_l_1380_, 3);
lean_dec(v_unused_1997_);
v_unused_1998_ = lean_ctor_get(v_l_1380_, 0);
lean_dec(v_unused_1998_);
v___x_1986_ = v_l_1380_;
v_isShared_1987_ = v_isSharedCheck_1995_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_v_1984_);
lean_inc(v_k_1983_);
lean_dec(v_l_1380_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1995_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1988_ = lean_unsigned_to_nat(3u);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 3, v_r_1964_);
lean_ctor_set(v___x_1986_, 2, v_v_1379_);
lean_ctor_set(v___x_1986_, 1, v_k_1378_);
lean_ctor_set(v___x_1986_, 0, v___x_1872_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_r_1964_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_r_1964_);
v___x_1990_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v___x_1990_);
lean_ctor_set(v___x_1383_, 3, v_l_1963_);
lean_ctor_set(v___x_1383_, 2, v_v_1984_);
lean_ctor_set(v___x_1383_, 1, v_k_1983_);
lean_ctor_set(v___x_1383_, 0, v___x_1988_);
v___x_1992_ = v___x_1383_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v_l_1963_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
else
{
lean_object* v_r_1999_; 
v_r_1999_ = lean_ctor_get(v_l_1380_, 4);
lean_inc(v_r_1999_);
if (lean_obj_tag(v_r_1999_) == 0)
{
lean_object* v_k_2000_; lean_object* v_v_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2024_; 
lean_inc(v_l_1963_);
v_k_2000_ = lean_ctor_get(v_l_1380_, 1);
v_v_2001_ = lean_ctor_get(v_l_1380_, 2);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_l_1380_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; lean_object* v_unused_2026_; lean_object* v_unused_2027_; 
v_unused_2025_ = lean_ctor_get(v_l_1380_, 4);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_l_1380_, 3);
lean_dec(v_unused_2026_);
v_unused_2027_ = lean_ctor_get(v_l_1380_, 0);
lean_dec(v_unused_2027_);
v___x_2003_ = v_l_1380_;
v_isShared_2004_ = v_isSharedCheck_2024_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_v_2001_);
lean_inc(v_k_2000_);
lean_dec(v_l_1380_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2024_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v_k_2005_; lean_object* v_v_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2020_; 
v_k_2005_ = lean_ctor_get(v_r_1999_, 1);
v_v_2006_ = lean_ctor_get(v_r_1999_, 2);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_r_1999_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; lean_object* v_unused_2022_; lean_object* v_unused_2023_; 
v_unused_2021_ = lean_ctor_get(v_r_1999_, 4);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_r_1999_, 3);
lean_dec(v_unused_2022_);
v_unused_2023_ = lean_ctor_get(v_r_1999_, 0);
lean_dec(v_unused_2023_);
v___x_2008_ = v_r_1999_;
v_isShared_2009_ = v_isSharedCheck_2020_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_v_2006_);
lean_inc(v_k_2005_);
lean_dec(v_r_1999_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2020_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2010_ = lean_unsigned_to_nat(3u);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v_l_1963_);
lean_ctor_set(v___x_2008_, 3, v_l_1963_);
lean_ctor_set(v___x_2008_, 2, v_v_2001_);
lean_ctor_set(v___x_2008_, 1, v_k_2000_);
lean_ctor_set(v___x_2008_, 0, v___x_1872_);
v___x_2012_ = v___x_2008_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_k_2000_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_v_2001_);
lean_ctor_set(v_reuseFailAlloc_2019_, 3, v_l_1963_);
lean_ctor_set(v_reuseFailAlloc_2019_, 4, v_l_1963_);
v___x_2012_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 4, v_l_1963_);
lean_ctor_set(v___x_2003_, 2, v_v_1379_);
lean_ctor_set(v___x_2003_, 1, v_k_1378_);
lean_ctor_set(v___x_2003_, 0, v___x_1872_);
v___x_2014_ = v___x_2003_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_l_1963_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v_l_1963_);
v___x_2014_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v___x_2014_);
lean_ctor_set(v___x_1383_, 3, v___x_2012_);
lean_ctor_set(v___x_1383_, 2, v_v_2006_);
lean_ctor_set(v___x_1383_, 1, v_k_2005_);
lean_ctor_set(v___x_1383_, 0, v___x_2010_);
v___x_2016_ = v___x_1383_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_k_2005_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_v_2006_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = lean_unsigned_to_nat(2u);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_r_1999_);
lean_ctor_set(v___x_1383_, 0, v___x_2028_);
v___x_2030_ = v___x_1383_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_2031_, 3, v_l_1380_);
lean_ctor_set(v_reuseFailAlloc_2031_, 4, v_r_1999_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v___x_2033_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_l_1380_);
lean_ctor_set(v___x_1383_, 0, v___x_1872_);
v___x_2033_ = v___x_1383_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_l_1380_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_l_1380_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
}
else
{
return v_t_1377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2037_, lean_object* v_t_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2037_, v_t_2038_);
lean_dec(v_k_2037_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2040_, lean_object* v_v_2041_, lean_object* v_i_2042_){
_start:
{
lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = lean_array_get_size(v_xs_2040_);
v___x_2044_ = lean_nat_dec_lt(v_i_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; 
lean_dec(v_i_2042_);
v___x_2045_ = lean_box(0);
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; uint8_t v___x_2047_; 
v___x_2046_ = lean_array_fget_borrowed(v_xs_2040_, v_i_2042_);
v___x_2047_ = l_Lean_instBEqFVarId_beq(v___x_2046_, v_v_2041_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_unsigned_to_nat(1u);
v___x_2049_ = lean_nat_add(v_i_2042_, v___x_2048_);
lean_dec(v_i_2042_);
v_i_2042_ = v___x_2049_;
goto _start;
}
else
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_i_2042_);
return v___x_2051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2052_, lean_object* v_v_2053_, lean_object* v_i_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2052_, v_v_2053_, v_i_2054_);
lean_dec(v_v_2053_);
lean_dec_ref(v_xs_2052_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2056_, lean_object* v_v_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2056_, v_v_2057_, v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2060_, lean_object* v_v_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2060_, v_v_2061_);
lean_dec(v_v_2061_);
lean_dec_ref(v_xs_2060_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2063_, size_t v_x_2064_, lean_object* v_x_2065_){
_start:
{
if (lean_obj_tag(v_x_2063_) == 0)
{
lean_object* v_es_2066_; lean_object* v___x_2067_; size_t v___x_2068_; size_t v___x_2069_; size_t v___x_2070_; lean_object* v_j_2071_; lean_object* v_entry_2072_; 
v_es_2066_ = lean_ctor_get(v_x_2063_, 0);
v___x_2067_ = lean_box(2);
v___x_2068_ = ((size_t)5ULL);
v___x_2069_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__1);
v___x_2070_ = lean_usize_land(v_x_2064_, v___x_2069_);
v_j_2071_ = lean_usize_to_nat(v___x_2070_);
v_entry_2072_ = lean_array_get(v___x_2067_, v_es_2066_, v_j_2071_);
switch(lean_obj_tag(v_entry_2072_))
{
case 0:
{
lean_object* v_key_2073_; uint8_t v___x_2074_; 
v_key_2073_ = lean_ctor_get(v_entry_2072_, 0);
lean_inc(v_key_2073_);
lean_dec_ref(v_entry_2072_);
v___x_2074_ = l_Lean_instBEqFVarId_beq(v_x_2065_, v_key_2073_);
lean_dec(v_key_2073_);
if (v___x_2074_ == 0)
{
lean_dec(v_j_2071_);
return v_x_2063_;
}
else
{
lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2082_; 
lean_inc_ref(v_es_2066_);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_x_2063_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v_x_2063_, 0);
lean_dec(v_unused_2083_);
v___x_2076_ = v_x_2063_;
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
else
{
lean_dec(v_x_2063_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_array_set(v_es_2066_, v_j_2071_, v___x_2067_);
lean_dec(v_j_2071_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
case 1:
{
lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2117_; 
lean_inc_ref(v_es_2066_);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_x_2063_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v_x_2063_, 0);
lean_dec(v_unused_2118_);
v___x_2085_ = v_x_2063_;
v_isShared_2086_ = v_isSharedCheck_2117_;
goto v_resetjp_2084_;
}
else
{
lean_dec(v_x_2063_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2117_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_node_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2116_; 
v_node_2087_ = lean_ctor_get(v_entry_2072_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_entry_2072_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2089_ = v_entry_2072_;
v_isShared_2090_ = v_isSharedCheck_2116_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_node_2087_);
lean_dec(v_entry_2072_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2116_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_entries_2091_; size_t v___x_2092_; lean_object* v_newNode_2093_; lean_object* v___x_2094_; 
v_entries_2091_ = lean_array_set(v_es_2066_, v_j_2071_, v___x_2067_);
v___x_2092_ = lean_usize_shift_right(v_x_2064_, v___x_2068_);
v_newNode_2093_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2087_, v___x_2092_, v_x_2065_);
lean_inc_ref(v_newNode_2093_);
v___x_2094_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2093_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v___x_2096_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v_newNode_2093_);
v___x_2096_ = v___x_2089_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_newNode_2093_);
v___x_2096_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2097_ = lean_array_set(v_entries_2091_, v_j_2071_, v___x_2096_);
lean_dec(v_j_2071_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2097_);
v___x_2099_ = v___x_2085_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
else
{
lean_object* v_val_2102_; lean_object* v_fst_2103_; lean_object* v_snd_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref(v_newNode_2093_);
lean_del_object(v___x_2089_);
v_val_2102_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_val_2102_);
lean_dec_ref(v___x_2094_);
v_fst_2103_ = lean_ctor_get(v_val_2102_, 0);
v_snd_2104_ = lean_ctor_get(v_val_2102_, 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_val_2102_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2106_ = v_val_2102_;
v_isShared_2107_ = v_isSharedCheck_2115_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_snd_2104_);
lean_inc(v_fst_2103_);
lean_dec(v_val_2102_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2115_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_fst_2103_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_snd_2104_);
v___x_2109_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = lean_array_set(v_entries_2091_, v_j_2071_, v___x_2109_);
lean_dec(v_j_2071_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2110_);
v___x_2112_ = v___x_2085_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2071_);
return v_x_2063_;
}
}
}
else
{
lean_object* v_ks_2119_; lean_object* v_vs_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2134_; 
v_ks_2119_ = lean_ctor_get(v_x_2063_, 0);
v_vs_2120_ = lean_ctor_get(v_x_2063_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_x_2063_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2122_ = v_x_2063_;
v_isShared_2123_ = v_isSharedCheck_2134_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_vs_2120_);
lean_inc(v_ks_2119_);
lean_dec(v_x_2063_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2134_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2119_, v_x_2065_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v___x_2126_; 
if (v_isShared_2123_ == 0)
{
v___x_2126_ = v___x_2122_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_ks_2119_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_vs_2120_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
else
{
lean_object* v_val_2128_; lean_object* v_keys_x27_2129_; lean_object* v_vals_x27_2130_; lean_object* v___x_2132_; 
v_val_2128_ = lean_ctor_get(v___x_2124_, 0);
lean_inc_n(v_val_2128_, 2);
lean_dec_ref(v___x_2124_);
v_keys_x27_2129_ = l_Array_eraseIdx___redArg(v_ks_2119_, v_val_2128_);
v_vals_x27_2130_ = l_Array_eraseIdx___redArg(v_vs_2120_, v_val_2128_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 1, v_vals_x27_2130_);
lean_ctor_set(v___x_2122_, 0, v_keys_x27_2129_);
v___x_2132_ = v___x_2122_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_keys_x27_2129_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_vals_x27_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2135_, lean_object* v_x_2136_, lean_object* v_x_2137_){
_start:
{
size_t v_x_2695__boxed_2138_; lean_object* v_res_2139_; 
v_x_2695__boxed_2138_ = lean_unbox_usize(v_x_2136_);
lean_dec(v_x_2136_);
v_res_2139_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2135_, v_x_2695__boxed_2138_, v_x_2137_);
lean_dec(v_x_2137_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2140_, lean_object* v_x_2141_){
_start:
{
uint64_t v___x_2142_; size_t v_h_2143_; lean_object* v___x_2144_; 
v___x_2142_ = l_Lean_instHashableFVarId_hash(v_x_2141_);
v_h_2143_ = lean_uint64_to_usize(v___x_2142_);
v___x_2144_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2140_, v_h_2143_, v_x_2141_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2145_, v_x_2146_);
lean_dec(v_x_2146_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object* v_lctx_2148_, lean_object* v_fvarId_2149_){
_start:
{
lean_object* v_fvarIdToDecl_2150_; lean_object* v_decls_2151_; lean_object* v_auxDeclToFullName_2152_; lean_object* v___x_2153_; 
v_fvarIdToDecl_2150_ = lean_ctor_get(v_lctx_2148_, 0);
v_decls_2151_ = lean_ctor_get(v_lctx_2148_, 1);
v_auxDeclToFullName_2152_ = lean_ctor_get(v_lctx_2148_, 2);
v___x_2153_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2150_, v_fvarId_2149_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_dec(v_fvarId_2149_);
return v_lctx_2148_;
}
else
{
lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2173_; 
lean_inc(v_auxDeclToFullName_2152_);
lean_inc_ref(v_decls_2151_);
lean_inc_ref(v_fvarIdToDecl_2150_);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_lctx_2148_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; lean_object* v_unused_2175_; lean_object* v_unused_2176_; 
v_unused_2174_ = lean_ctor_get(v_lctx_2148_, 2);
lean_dec(v_unused_2174_);
v_unused_2175_ = lean_ctor_get(v_lctx_2148_, 1);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_lctx_2148_, 0);
lean_dec(v_unused_2176_);
v___x_2155_ = v_lctx_2148_;
v_isShared_2156_ = v_isSharedCheck_2173_;
goto v_resetjp_2154_;
}
else
{
lean_dec(v_lctx_2148_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2173_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v_val_2157_; lean_object* v___x_2158_; lean_object* v___y_2160_; lean_object* v_index_2172_; 
v_val_2157_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_val_2157_);
lean_dec_ref(v___x_2153_);
v___x_2158_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2150_, v_fvarId_2149_);
v_index_2172_ = lean_ctor_get(v_val_2157_, 0);
lean_inc(v_index_2172_);
v___y_2160_ = v_index_2172_;
goto v___jp_2159_;
v___jp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2161_ = lean_box(0);
v___x_2162_ = l_Lean_PersistentArray_set___redArg(v_decls_2151_, v___y_2160_, v___x_2161_);
lean_dec(v___y_2160_);
v___x_2163_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2162_);
v___x_2164_ = l_Lean_LocalDecl_isAuxDecl(v_val_2157_);
lean_dec(v_val_2157_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2166_; 
lean_dec(v_fvarId_2149_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v___x_2163_);
lean_ctor_set(v___x_2155_, 0, v___x_2158_);
v___x_2166_ = v___x_2155_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_auxDeclToFullName_2152_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2149_, v_auxDeclToFullName_2152_);
lean_dec(v_fvarId_2149_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 2, v___x_2168_);
lean_ctor_set(v___x_2155_, 1, v___x_2163_);
lean_ctor_set(v___x_2155_, 0, v___x_2158_);
v___x_2170_ = v___x_2155_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2177_, lean_object* v_x_2178_, lean_object* v_x_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2178_, v_x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2181_, v_x_2182_, v_x_2183_);
lean_dec(v_x_2183_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2185_, lean_object* v_k_2186_, lean_object* v_t_2187_, lean_object* v_h_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2186_, v_t_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2190_, lean_object* v_k_2191_, lean_object* v_t_2192_, lean_object* v_h_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2190_, v_k_2191_, v_t_2192_, v_h_2193_);
lean_dec(v_k_2191_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2195_, lean_object* v_x_2196_, size_t v_x_2197_, lean_object* v_x_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2196_, v_x_2197_, v_x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
size_t v_x_2919__boxed_2204_; lean_object* v_res_2205_; 
v_x_2919__boxed_2204_ = lean_unbox_usize(v_x_2202_);
lean_dec(v_x_2202_);
v_res_2205_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2200_, v_x_2201_, v_x_2919__boxed_2204_, v_x_2203_);
lean_dec(v_x_2203_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2206_){
_start:
{
lean_object* v_decls_2207_; lean_object* v_fvarIdToDecl_2208_; lean_object* v_auxDeclToFullName_2209_; lean_object* v_size_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v_decls_2207_ = lean_ctor_get(v_lctx_2206_, 1);
v_fvarIdToDecl_2208_ = lean_ctor_get(v_lctx_2206_, 0);
v_auxDeclToFullName_2209_ = lean_ctor_get(v_lctx_2206_, 2);
v_size_2210_ = lean_ctor_get(v_decls_2207_, 2);
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = lean_nat_dec_eq(v_size_2210_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_unsigned_to_nat(1u);
v___x_2215_ = lean_nat_sub(v_size_2210_, v___x_2214_);
v___x_2216_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2213_, v_decls_2207_, v___x_2215_);
lean_dec(v___x_2215_);
if (lean_obj_tag(v___x_2216_) == 0)
{
return v_lctx_2206_;
}
else
{
lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2235_; 
lean_inc(v_auxDeclToFullName_2209_);
lean_inc_ref(v_fvarIdToDecl_2208_);
lean_inc_ref(v_decls_2207_);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_lctx_2206_);
if (v_isSharedCheck_2235_ == 0)
{
lean_object* v_unused_2236_; lean_object* v_unused_2237_; lean_object* v_unused_2238_; 
v_unused_2236_ = lean_ctor_get(v_lctx_2206_, 2);
lean_dec(v_unused_2236_);
v_unused_2237_ = lean_ctor_get(v_lctx_2206_, 1);
lean_dec(v_unused_2237_);
v_unused_2238_ = lean_ctor_get(v_lctx_2206_, 0);
lean_dec(v_unused_2238_);
v___x_2218_ = v_lctx_2206_;
v_isShared_2219_ = v_isSharedCheck_2235_;
goto v_resetjp_2217_;
}
else
{
lean_dec(v_lctx_2206_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2235_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v_val_2220_; lean_object* v___y_2222_; lean_object* v_fvarId_2234_; 
v_val_2220_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_val_2220_);
lean_dec_ref(v___x_2216_);
v_fvarId_2234_ = lean_ctor_get(v_val_2220_, 1);
lean_inc(v_fvarId_2234_);
v___y_2222_ = v_fvarId_2234_;
goto v___jp_2221_;
v___jp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2223_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2208_, v___y_2222_);
v___x_2224_ = l_Lean_PersistentArray_pop___redArg(v_decls_2207_);
v___x_2225_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2224_);
v___x_2226_ = l_Lean_LocalDecl_isAuxDecl(v_val_2220_);
lean_dec(v_val_2220_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2228_; 
lean_dec(v___y_2222_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2225_);
lean_ctor_set(v___x_2218_, 0, v___x_2223_);
v___x_2228_ = v___x_2218_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_auxDeclToFullName_2209_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2230_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2222_, v_auxDeclToFullName_2209_);
lean_dec(v___y_2222_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 2, v___x_2230_);
lean_ctor_set(v___x_2218_, 1, v___x_2225_);
lean_ctor_set(v___x_2218_, 0, v___x_2223_);
v___x_2232_ = v___x_2218_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
}
else
{
return v_lctx_2206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2239_, lean_object* v_as_2240_, lean_object* v_i_2241_){
_start:
{
lean_object* v_zero_2242_; uint8_t v_isZero_2243_; 
v_zero_2242_ = lean_unsigned_to_nat(0u);
v_isZero_2243_ = lean_nat_dec_eq(v_i_2241_, v_zero_2242_);
if (v_isZero_2243_ == 1)
{
lean_object* v___x_2244_; 
lean_dec(v_i_2241_);
v___x_2244_ = lean_box(0);
return v___x_2244_;
}
else
{
lean_object* v_one_2245_; lean_object* v_n_2246_; lean_object* v___y_2248_; lean_object* v___x_2250_; lean_object* v___y_2252_; 
v_one_2245_ = lean_unsigned_to_nat(1u);
v_n_2246_ = lean_nat_sub(v_i_2241_, v_one_2245_);
lean_dec(v_i_2241_);
v___x_2250_ = lean_array_fget_borrowed(v_as_2240_, v_n_2246_);
if (lean_obj_tag(v___x_2250_) == 0)
{
v___y_2248_ = v___x_2250_;
goto v___jp_2247_;
}
else
{
lean_object* v_val_2255_; lean_object* v_userName_2256_; 
v_val_2255_ = lean_ctor_get(v___x_2250_, 0);
v_userName_2256_ = lean_ctor_get(v_val_2255_, 2);
v___y_2252_ = v_userName_2256_;
goto v___jp_2251_;
}
v___jp_2247_:
{
if (lean_obj_tag(v___y_2248_) == 0)
{
v_i_2241_ = v_n_2246_;
goto _start;
}
else
{
lean_dec(v_n_2246_);
lean_inc_ref(v___y_2248_);
return v___y_2248_;
}
}
v___jp_2251_:
{
uint8_t v___x_2253_; 
v___x_2253_ = lean_name_eq(v___y_2252_, v_userName_2239_);
if (v___x_2253_ == 0)
{
v_i_2241_ = v_n_2246_;
goto _start;
}
else
{
v___y_2248_ = v___x_2250_;
goto v___jp_2247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2257_, lean_object* v_as_2258_, lean_object* v_i_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2257_, v_as_2258_, v_i_2259_);
lean_dec_ref(v_as_2258_);
lean_dec(v_userName_2257_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2261_, lean_object* v_as_2262_, lean_object* v_i_2263_){
_start:
{
lean_object* v_zero_2264_; uint8_t v_isZero_2265_; 
v_zero_2264_ = lean_unsigned_to_nat(0u);
v_isZero_2265_ = lean_nat_dec_eq(v_i_2263_, v_zero_2264_);
if (v_isZero_2265_ == 1)
{
lean_object* v___x_2266_; 
lean_dec(v_i_2263_);
v___x_2266_ = lean_box(0);
return v___x_2266_;
}
else
{
lean_object* v_one_2267_; lean_object* v_n_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_one_2267_ = lean_unsigned_to_nat(1u);
v_n_2268_ = lean_nat_sub(v_i_2263_, v_one_2267_);
lean_dec(v_i_2263_);
v___x_2269_ = lean_array_fget_borrowed(v_as_2262_, v_n_2268_);
v___x_2270_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2261_, v___x_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
v_i_2263_ = v_n_2268_;
goto _start;
}
else
{
lean_dec(v_n_2268_);
return v___x_2270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2272_, lean_object* v_x_2273_){
_start:
{
if (lean_obj_tag(v_x_2273_) == 0)
{
lean_object* v_cs_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v_cs_2274_ = lean_ctor_get(v_x_2273_, 0);
v___x_2275_ = lean_array_get_size(v_cs_2274_);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2272_, v_cs_2274_, v___x_2275_);
return v___x_2276_;
}
else
{
lean_object* v_vs_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_vs_2277_ = lean_ctor_get(v_x_2273_, 0);
v___x_2278_ = lean_array_get_size(v_vs_2277_);
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2272_, v_vs_2277_, v___x_2278_);
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2280_, lean_object* v_x_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2280_, v_x_2281_);
lean_dec_ref(v_x_2281_);
lean_dec(v_userName_2280_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2283_, lean_object* v_as_2284_, lean_object* v_i_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2283_, v_as_2284_, v_i_2285_);
lean_dec_ref(v_as_2284_);
lean_dec(v_userName_2283_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2287_, lean_object* v_t_2288_){
_start:
{
lean_object* v_root_2289_; lean_object* v_tail_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_root_2289_ = lean_ctor_get(v_t_2288_, 0);
v_tail_2290_ = lean_ctor_get(v_t_2288_, 1);
v___x_2291_ = lean_array_get_size(v_tail_2290_);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2287_, v_tail_2290_, v___x_2291_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2287_, v_root_2289_);
return v___x_2293_;
}
else
{
return v___x_2292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2294_, lean_object* v_t_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2294_, v_t_2295_);
lean_dec_ref(v_t_2295_);
lean_dec(v_userName_2294_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2297_, lean_object* v_userName_2298_){
_start:
{
lean_object* v_decls_2299_; lean_object* v___x_2300_; 
v_decls_2299_ = lean_ctor_get(v_lctx_2297_, 1);
v___x_2300_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2298_, v_decls_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2301_, lean_object* v_userName_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2301_, v_userName_2302_);
lean_dec(v_userName_2302_);
lean_dec_ref(v_lctx_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2304_, lean_object* v_as_2305_, lean_object* v_i_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2304_, v_as_2305_, v_i_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2309_, lean_object* v_as_2310_, lean_object* v_i_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2309_, v_as_2310_, v_i_2311_, v_a_2312_);
lean_dec_ref(v_as_2310_);
lean_dec(v_userName_2309_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2314_, lean_object* v_as_2315_, lean_object* v_i_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2314_, v_as_2315_, v_i_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2319_, lean_object* v_as_2320_, lean_object* v_i_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2319_, v_as_2320_, v_i_2321_, v_a_2322_);
lean_dec_ref(v_as_2320_);
lean_dec(v_userName_2319_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2327_, lean_object* v_userName_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2327_, v_userName_2328_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2330_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2331_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2332_ = lean_unsigned_to_nat(403u);
v___x_2333_ = lean_unsigned_to_nat(17u);
v___x_2334_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2335_ = 1;
v___x_2336_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2328_, v___x_2335_);
v___x_2337_ = lean_string_append(v___x_2334_, v___x_2336_);
lean_dec_ref(v___x_2336_);
v___x_2338_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2339_ = lean_string_append(v___x_2337_, v___x_2338_);
v___x_2340_ = l_mkPanicMessageWithDecl(v___x_2330_, v___x_2331_, v___x_2332_, v___x_2333_, v___x_2339_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2340_);
return v___x_2341_;
}
else
{
lean_object* v_val_2342_; 
lean_dec(v_userName_2328_);
v_val_2342_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_val_2342_);
lean_dec_ref(v___x_2329_);
return v_val_2342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2343_, lean_object* v_userName_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2343_, v_userName_2344_);
lean_dec_ref(v_lctx_2343_);
return v_res_2345_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2346_, lean_object* v_userName_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2346_, v_userName_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
uint8_t v___x_2349_; 
v___x_2349_ = 0;
return v___x_2349_;
}
else
{
uint8_t v___x_2350_; 
lean_dec_ref(v___x_2348_);
v___x_2350_ = 1;
return v___x_2350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2351_, lean_object* v_userName_2352_){
_start:
{
uint8_t v_res_2353_; lean_object* v_r_2354_; 
v_res_2353_ = l_Lean_LocalContext_usesUserName(v_lctx_2351_, v_userName_2352_);
lean_dec(v_userName_2352_);
lean_dec_ref(v_lctx_2351_);
v_r_2354_ = lean_box(v_res_2353_);
return v_r_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2355_, lean_object* v_suggestion_2356_, lean_object* v_i_2357_){
_start:
{
lean_object* v_curr_2358_; uint8_t v___x_2359_; 
lean_inc(v_i_2357_);
lean_inc(v_suggestion_2356_);
v_curr_2358_ = lean_name_append_index_after(v_suggestion_2356_, v_i_2357_);
v___x_2359_ = l_Lean_LocalContext_usesUserName(v_lctx_2355_, v_curr_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec(v_suggestion_2356_);
v___x_2360_ = lean_unsigned_to_nat(1u);
v___x_2361_ = lean_nat_add(v_i_2357_, v___x_2360_);
lean_dec(v_i_2357_);
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v_curr_2358_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
return v___x_2362_;
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec(v_curr_2358_);
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = lean_nat_add(v_i_2357_, v___x_2363_);
lean_dec(v_i_2357_);
v_i_2357_ = v___x_2364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2366_, lean_object* v_suggestion_2367_, lean_object* v_i_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2366_, v_suggestion_2367_, v_i_2368_);
lean_dec_ref(v_lctx_2366_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2370_, lean_object* v_suggestion_2371_){
_start:
{
lean_object* v_suggestion_2372_; uint8_t v___x_2373_; 
v_suggestion_2372_ = lean_erase_macro_scopes(v_suggestion_2371_);
v___x_2373_ = l_Lean_LocalContext_usesUserName(v_lctx_2370_, v_suggestion_2372_);
if (v___x_2373_ == 0)
{
return v_suggestion_2372_;
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v_fst_2376_; 
v___x_2374_ = lean_unsigned_to_nat(1u);
v___x_2375_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2370_, v_suggestion_2372_, v___x_2374_);
v_fst_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_fst_2376_);
lean_dec_ref(v___x_2375_);
return v_fst_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2377_, lean_object* v_suggestion_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_LocalContext_getUnusedName(v_lctx_2377_, v_suggestion_2378_);
lean_dec_ref(v_lctx_2377_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2380_){
_start:
{
lean_object* v_decls_2381_; lean_object* v_size_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v_decls_2381_ = lean_ctor_get(v_lctx_2380_, 1);
v_size_2382_ = lean_ctor_get(v_decls_2381_, 2);
v___x_2383_ = lean_box(0);
v___x_2384_ = lean_unsigned_to_nat(1u);
v___x_2385_ = lean_nat_sub(v_size_2382_, v___x_2384_);
v___x_2386_ = lean_nat_dec_lt(v___x_2385_, v_size_2382_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; 
lean_dec(v___x_2385_);
v___x_2387_ = l_outOfBounds___redArg(v___x_2383_);
return v___x_2387_;
}
else
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2383_, v_decls_2381_, v___x_2385_);
lean_dec(v___x_2385_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object* v_lctx_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_LocalContext_lastDecl(v_lctx_2389_);
lean_dec_ref(v_lctx_2389_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2391_, lean_object* v_fvarId_2392_, lean_object* v_userName_2393_){
_start:
{
lean_object* v_fvarIdToDecl_2394_; lean_object* v_decls_2395_; lean_object* v_auxDeclToFullName_2396_; lean_object* v_decl_2397_; lean_object* v_decl_2398_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2406_; lean_object* v_fvarId_2409_; 
v_fvarIdToDecl_2394_ = lean_ctor_get(v_lctx_2391_, 0);
lean_inc_ref(v_fvarIdToDecl_2394_);
v_decls_2395_ = lean_ctor_get(v_lctx_2391_, 1);
lean_inc_ref(v_decls_2395_);
v_auxDeclToFullName_2396_ = lean_ctor_get(v_lctx_2391_, 2);
lean_inc(v_auxDeclToFullName_2396_);
v_decl_2397_ = l_Lean_LocalContext_get_x21(v_lctx_2391_, v_fvarId_2392_);
v_decl_2398_ = l_Lean_LocalDecl_setUserName(v_decl_2397_, v_userName_2393_);
v_fvarId_2409_ = lean_ctor_get(v_decl_2398_, 1);
lean_inc(v_fvarId_2409_);
v___y_2406_ = v_fvarId_2409_;
goto v___jp_2405_;
v___jp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2402_, 0, v_decl_2398_);
v___x_2403_ = l_Lean_PersistentArray_set___redArg(v_decls_2395_, v___y_2401_, v___x_2402_);
lean_dec(v___y_2401_);
v___x_2404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2404_, 0, v___y_2400_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
lean_ctor_set(v___x_2404_, 2, v_auxDeclToFullName_2396_);
return v___x_2404_;
}
v___jp_2405_:
{
lean_object* v___x_2407_; lean_object* v_index_2408_; 
lean_inc_ref(v_decl_2398_);
v___x_2407_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2394_, v___y_2406_, v_decl_2398_);
v_index_2408_ = lean_ctor_get(v_decl_2398_, 0);
lean_inc(v_index_2408_);
v___y_2400_ = v___x_2407_;
v___y_2401_ = v_index_2408_;
goto v___jp_2399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2410_, lean_object* v_fromName_2411_, lean_object* v_toName_2412_){
_start:
{
lean_object* v_fvarIdToDecl_2413_; lean_object* v_decls_2414_; lean_object* v_auxDeclToFullName_2415_; lean_object* v___x_2416_; 
v_fvarIdToDecl_2413_ = lean_ctor_get(v_lctx_2410_, 0);
v_decls_2414_ = lean_ctor_get(v_lctx_2410_, 1);
v_auxDeclToFullName_2415_ = lean_ctor_get(v_lctx_2410_, 2);
v___x_2416_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2410_, v_fromName_2411_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_dec(v_toName_2412_);
return v_lctx_2410_;
}
else
{
lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2441_; 
lean_inc(v_auxDeclToFullName_2415_);
lean_inc_ref(v_decls_2414_);
lean_inc_ref(v_fvarIdToDecl_2413_);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_lctx_2410_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; lean_object* v_unused_2443_; lean_object* v_unused_2444_; 
v_unused_2442_ = lean_ctor_get(v_lctx_2410_, 2);
lean_dec(v_unused_2442_);
v_unused_2443_ = lean_ctor_get(v_lctx_2410_, 1);
lean_dec(v_unused_2443_);
v_unused_2444_ = lean_ctor_get(v_lctx_2410_, 0);
lean_dec(v_unused_2444_);
v___x_2418_ = v_lctx_2410_;
v_isShared_2419_ = v_isSharedCheck_2441_;
goto v_resetjp_2417_;
}
else
{
lean_dec(v_lctx_2410_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2441_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_val_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2440_; 
v_val_2420_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2422_ = v___x_2416_;
v_isShared_2423_ = v_isSharedCheck_2440_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_val_2420_);
lean_dec(v___x_2416_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2440_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_decl_2424_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2436_; lean_object* v_fvarId_2439_; 
v_decl_2424_ = l_Lean_LocalDecl_setUserName(v_val_2420_, v_toName_2412_);
v_fvarId_2439_ = lean_ctor_get(v_decl_2424_, 1);
lean_inc(v_fvarId_2439_);
v___y_2436_ = v_fvarId_2439_;
goto v___jp_2435_;
v___jp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v_decl_2424_);
v___x_2429_ = v___x_2422_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_decl_2424_);
v___x_2429_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2430_ = l_Lean_PersistentArray_set___redArg(v_decls_2414_, v___y_2427_, v___x_2429_);
lean_dec(v___y_2427_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 1, v___x_2430_);
lean_ctor_set(v___x_2418_, 0, v___y_2426_);
v___x_2432_ = v___x_2418_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___y_2426_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2433_, 2, v_auxDeclToFullName_2415_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
v___jp_2435_:
{
lean_object* v___x_2437_; lean_object* v_index_2438_; 
lean_inc_ref(v_decl_2424_);
v___x_2437_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2413_, v___y_2436_, v_decl_2424_);
v_index_2438_ = lean_ctor_get(v_decl_2424_, 0);
lean_inc(v_index_2438_);
v___y_2426_ = v___x_2437_;
v___y_2427_ = v_index_2438_;
goto v___jp_2425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2445_, lean_object* v_fromName_2446_, lean_object* v_toName_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_LocalContext_renameUserName(v_lctx_2445_, v_fromName_2446_, v_toName_2447_);
lean_dec(v_fromName_2446_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2451_, lean_object* v_fvarId_2452_, lean_object* v_f_2453_){
_start:
{
lean_object* v_fvarIdToDecl_2454_; lean_object* v_decls_2455_; lean_object* v_auxDeclToFullName_2456_; lean_object* v___x_2457_; 
v_fvarIdToDecl_2454_ = lean_ctor_get(v_lctx_2451_, 0);
v_decls_2455_ = lean_ctor_get(v_lctx_2451_, 1);
v_auxDeclToFullName_2456_ = lean_ctor_get(v_lctx_2451_, 2);
lean_inc_ref(v_lctx_2451_);
v___x_2457_ = lean_local_ctx_find(v_lctx_2451_, v_fvarId_2452_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_dec_ref(v_f_2453_);
return v_lctx_2451_;
}
else
{
lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2484_; 
lean_inc(v_auxDeclToFullName_2456_);
lean_inc_ref(v_decls_2455_);
lean_inc_ref(v_fvarIdToDecl_2454_);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_lctx_2451_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; lean_object* v_unused_2486_; lean_object* v_unused_2487_; 
v_unused_2485_ = lean_ctor_get(v_lctx_2451_, 2);
lean_dec(v_unused_2485_);
v_unused_2486_ = lean_ctor_get(v_lctx_2451_, 1);
lean_dec(v_unused_2486_);
v_unused_2487_ = lean_ctor_get(v_lctx_2451_, 0);
lean_dec(v_unused_2487_);
v___x_2459_ = v_lctx_2451_;
v_isShared_2460_ = v_isSharedCheck_2484_;
goto v_resetjp_2458_;
}
else
{
lean_dec(v_lctx_2451_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2484_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v_val_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2483_; 
v_val_2461_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2463_ = v___x_2457_;
v_isShared_2464_ = v_isSharedCheck_2483_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_val_2461_);
lean_dec(v___x_2457_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2483_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v_decl_2467_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2479_; lean_object* v_fvarId_2482_; 
v___x_2465_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2466_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2467_ = lean_apply_1(v_f_2453_, v_val_2461_);
v_fvarId_2482_ = lean_ctor_get(v_decl_2467_, 1);
lean_inc(v_fvarId_2482_);
v___y_2479_ = v_fvarId_2482_;
goto v___jp_2478_;
v___jp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v_decl_2467_);
v___x_2472_ = v___x_2463_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_decl_2467_);
v___x_2472_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = l_Lean_PersistentArray_set___redArg(v_decls_2455_, v___y_2470_, v___x_2472_);
lean_dec(v___y_2470_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 1, v___x_2473_);
lean_ctor_set(v___x_2459_, 0, v___y_2469_);
v___x_2475_ = v___x_2459_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___y_2469_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v_auxDeclToFullName_2456_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
v___jp_2478_:
{
lean_object* v___x_2480_; lean_object* v_index_2481_; 
lean_inc_ref(v_decl_2467_);
v___x_2480_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2465_, v___x_2466_, v_fvarIdToDecl_2454_, v___y_2479_, v_decl_2467_);
v_index_2481_ = lean_ctor_get(v_decl_2467_, 0);
lean_inc(v_index_2481_);
v___y_2469_ = v___x_2480_;
v___y_2470_ = v_index_2481_;
goto v___jp_2468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2488_, lean_object* v_as_2489_, size_t v_i_2490_, size_t v_stop_2491_, lean_object* v_b_2492_){
_start:
{
lean_object* v___y_2494_; uint8_t v___x_2498_; 
v___x_2498_ = lean_usize_dec_eq(v_i_2490_, v_stop_2491_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_array_uget(v_as_2489_, v_i_2490_);
if (lean_obj_tag(v___x_2499_) == 0)
{
v___y_2494_ = v_b_2492_;
goto v___jp_2493_;
}
else
{
lean_object* v_val_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2527_; 
v_val_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2527_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_val_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2527_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_fvarIdToDecl_2504_; lean_object* v_decls_2505_; lean_object* v_auxDeclToFullName_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2526_; 
v_fvarIdToDecl_2504_ = lean_ctor_get(v_b_2492_, 0);
v_decls_2505_ = lean_ctor_get(v_b_2492_, 1);
v_auxDeclToFullName_2506_ = lean_ctor_get(v_b_2492_, 2);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_b_2492_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2508_ = v_b_2492_;
v_isShared_2509_ = v_isSharedCheck_2526_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_auxDeclToFullName_2506_);
lean_inc(v_decls_2505_);
lean_inc(v_fvarIdToDecl_2504_);
lean_dec(v_b_2492_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2526_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v_decl_2510_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2522_; lean_object* v_fvarId_2525_; 
lean_inc_ref(v_f_2488_);
v_decl_2510_ = lean_apply_1(v_f_2488_, v_val_2500_);
v_fvarId_2525_ = lean_ctor_get(v_decl_2510_, 1);
lean_inc(v_fvarId_2525_);
v___y_2522_ = v_fvarId_2525_;
goto v___jp_2521_;
v___jp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v_decl_2510_);
v___x_2515_ = v___x_2502_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_decl_2510_);
v___x_2515_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = l_Lean_PersistentArray_set___redArg(v_decls_2505_, v___y_2513_, v___x_2515_);
lean_dec(v___y_2513_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v___x_2516_);
lean_ctor_set(v___x_2508_, 0, v___y_2512_);
v___x_2518_ = v___x_2508_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___y_2512_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_auxDeclToFullName_2506_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
v___y_2494_ = v___x_2518_;
goto v___jp_2493_;
}
}
}
v___jp_2521_:
{
lean_object* v___x_2523_; lean_object* v_index_2524_; 
lean_inc_ref(v_decl_2510_);
v___x_2523_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2504_, v___y_2522_, v_decl_2510_);
v_index_2524_ = lean_ctor_get(v_decl_2510_, 0);
lean_inc(v_index_2524_);
v___y_2512_ = v___x_2523_;
v___y_2513_ = v_index_2524_;
goto v___jp_2511_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_2488_);
return v_b_2492_;
}
v___jp_2493_:
{
size_t v___x_2495_; size_t v___x_2496_; 
v___x_2495_ = ((size_t)1ULL);
v___x_2496_ = lean_usize_add(v_i_2490_, v___x_2495_);
v_i_2490_ = v___x_2496_;
v_b_2492_ = v___y_2494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2528_, lean_object* v_as_2529_, lean_object* v_i_2530_, lean_object* v_stop_2531_, lean_object* v_b_2532_){
_start:
{
size_t v_i_boxed_2533_; size_t v_stop_boxed_2534_; lean_object* v_res_2535_; 
v_i_boxed_2533_ = lean_unbox_usize(v_i_2530_);
lean_dec(v_i_2530_);
v_stop_boxed_2534_ = lean_unbox_usize(v_stop_2531_);
lean_dec(v_stop_2531_);
v_res_2535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2528_, v_as_2529_, v_i_boxed_2533_, v_stop_boxed_2534_, v_b_2532_);
lean_dec_ref(v_as_2529_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2536_, lean_object* v_x_2537_, lean_object* v_x_2538_){
_start:
{
if (lean_obj_tag(v_x_2537_) == 0)
{
lean_object* v_cs_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v_cs_2539_ = lean_ctor_get(v_x_2537_, 0);
v___x_2540_ = lean_unsigned_to_nat(0u);
v___x_2541_ = lean_array_get_size(v_cs_2539_);
v___x_2542_ = lean_nat_dec_lt(v___x_2540_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_dec_ref(v_f_2536_);
return v_x_2538_;
}
else
{
uint8_t v___x_2543_; 
v___x_2543_ = lean_nat_dec_le(v___x_2541_, v___x_2541_);
if (v___x_2543_ == 0)
{
if (v___x_2542_ == 0)
{
lean_dec_ref(v_f_2536_);
return v_x_2538_;
}
else
{
size_t v___x_2544_; size_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = ((size_t)0ULL);
v___x_2545_ = lean_usize_of_nat(v___x_2541_);
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2536_, v_cs_2539_, v___x_2544_, v___x_2545_, v_x_2538_);
return v___x_2546_;
}
}
else
{
size_t v___x_2547_; size_t v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = lean_usize_of_nat(v___x_2541_);
v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2536_, v_cs_2539_, v___x_2547_, v___x_2548_, v_x_2538_);
return v___x_2549_;
}
}
}
else
{
lean_object* v_vs_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v_vs_2550_ = lean_ctor_get(v_x_2537_, 0);
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = lean_array_get_size(v_vs_2550_);
v___x_2553_ = lean_nat_dec_lt(v___x_2551_, v___x_2552_);
if (v___x_2553_ == 0)
{
lean_dec_ref(v_f_2536_);
return v_x_2538_;
}
else
{
uint8_t v___x_2554_; 
v___x_2554_ = lean_nat_dec_le(v___x_2552_, v___x_2552_);
if (v___x_2554_ == 0)
{
if (v___x_2553_ == 0)
{
lean_dec_ref(v_f_2536_);
return v_x_2538_;
}
else
{
size_t v___x_2555_; size_t v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = ((size_t)0ULL);
v___x_2556_ = lean_usize_of_nat(v___x_2552_);
v___x_2557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2536_, v_vs_2550_, v___x_2555_, v___x_2556_, v_x_2538_);
return v___x_2557_;
}
}
else
{
size_t v___x_2558_; size_t v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = ((size_t)0ULL);
v___x_2559_ = lean_usize_of_nat(v___x_2552_);
v___x_2560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2536_, v_vs_2550_, v___x_2558_, v___x_2559_, v_x_2538_);
return v___x_2560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2561_, lean_object* v_as_2562_, size_t v_i_2563_, size_t v_stop_2564_, lean_object* v_b_2565_){
_start:
{
uint8_t v___x_2566_; 
v___x_2566_ = lean_usize_dec_eq(v_i_2563_, v_stop_2564_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; size_t v___x_2569_; size_t v___x_2570_; 
v___x_2567_ = lean_array_uget_borrowed(v_as_2562_, v_i_2563_);
lean_inc_ref(v_f_2561_);
v___x_2568_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2561_, v___x_2567_, v_b_2565_);
v___x_2569_ = ((size_t)1ULL);
v___x_2570_ = lean_usize_add(v_i_2563_, v___x_2569_);
v_i_2563_ = v___x_2570_;
v_b_2565_ = v___x_2568_;
goto _start;
}
else
{
lean_dec_ref(v_f_2561_);
return v_b_2565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2572_, lean_object* v_as_2573_, lean_object* v_i_2574_, lean_object* v_stop_2575_, lean_object* v_b_2576_){
_start:
{
size_t v_i_boxed_2577_; size_t v_stop_boxed_2578_; lean_object* v_res_2579_; 
v_i_boxed_2577_ = lean_unbox_usize(v_i_2574_);
lean_dec(v_i_2574_);
v_stop_boxed_2578_ = lean_unbox_usize(v_stop_2575_);
lean_dec(v_stop_2575_);
v_res_2579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2572_, v_as_2573_, v_i_boxed_2577_, v_stop_boxed_2578_, v_b_2576_);
lean_dec_ref(v_as_2573_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2580_, lean_object* v_x_2581_, lean_object* v_x_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2580_, v_x_2581_, v_x_2582_);
lean_dec_ref(v_x_2581_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2584_, lean_object* v_x_2585_, size_t v_x_2586_, size_t v_x_2587_, lean_object* v_x_2588_){
_start:
{
if (lean_obj_tag(v_x_2585_) == 0)
{
lean_object* v_cs_2589_; lean_object* v___x_2590_; size_t v___x_2591_; lean_object* v_j_2592_; lean_object* v___x_2593_; size_t v___x_2594_; size_t v___x_2595_; size_t v___x_2596_; size_t v___x_2597_; size_t v___x_2598_; size_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v_cs_2589_ = lean_ctor_get(v_x_2585_, 0);
v___x_2590_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2591_ = lean_usize_shift_right(v_x_2586_, v_x_2587_);
v_j_2592_ = lean_usize_to_nat(v___x_2591_);
v___x_2593_ = lean_array_get_borrowed(v___x_2590_, v_cs_2589_, v_j_2592_);
v___x_2594_ = ((size_t)1ULL);
v___x_2595_ = lean_usize_shift_left(v___x_2594_, v_x_2587_);
v___x_2596_ = lean_usize_sub(v___x_2595_, v___x_2594_);
v___x_2597_ = lean_usize_land(v_x_2586_, v___x_2596_);
v___x_2598_ = ((size_t)5ULL);
v___x_2599_ = lean_usize_sub(v_x_2587_, v___x_2598_);
lean_inc_ref(v_f_2584_);
v___x_2600_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2584_, v___x_2593_, v___x_2597_, v___x_2599_, v_x_2588_);
v___x_2601_ = lean_unsigned_to_nat(1u);
v___x_2602_ = lean_nat_add(v_j_2592_, v___x_2601_);
lean_dec(v_j_2592_);
v___x_2603_ = lean_array_get_size(v_cs_2589_);
v___x_2604_ = lean_nat_dec_lt(v___x_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_dec(v___x_2602_);
lean_dec_ref(v_f_2584_);
return v___x_2600_;
}
else
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_nat_dec_le(v___x_2603_, v___x_2603_);
if (v___x_2605_ == 0)
{
if (v___x_2604_ == 0)
{
lean_dec(v___x_2602_);
lean_dec_ref(v_f_2584_);
return v___x_2600_;
}
else
{
size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = lean_usize_of_nat(v___x_2602_);
lean_dec(v___x_2602_);
v___x_2607_ = lean_usize_of_nat(v___x_2603_);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2584_, v_cs_2589_, v___x_2606_, v___x_2607_, v___x_2600_);
return v___x_2608_;
}
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_usize_of_nat(v___x_2602_);
lean_dec(v___x_2602_);
v___x_2610_ = lean_usize_of_nat(v___x_2603_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2584_, v_cs_2589_, v___x_2609_, v___x_2610_, v___x_2600_);
return v___x_2611_;
}
}
}
else
{
lean_object* v_vs_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v_vs_2612_ = lean_ctor_get(v_x_2585_, 0);
v___x_2613_ = lean_usize_to_nat(v_x_2586_);
v___x_2614_ = lean_array_get_size(v_vs_2612_);
v___x_2615_ = lean_nat_dec_lt(v___x_2613_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_dec(v___x_2613_);
lean_dec_ref(v_f_2584_);
return v_x_2588_;
}
else
{
uint8_t v___x_2616_; 
v___x_2616_ = lean_nat_dec_le(v___x_2614_, v___x_2614_);
if (v___x_2616_ == 0)
{
if (v___x_2615_ == 0)
{
lean_dec(v___x_2613_);
lean_dec_ref(v_f_2584_);
return v_x_2588_;
}
else
{
size_t v___x_2617_; size_t v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_usize_of_nat(v___x_2613_);
lean_dec(v___x_2613_);
v___x_2618_ = lean_usize_of_nat(v___x_2614_);
v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2584_, v_vs_2612_, v___x_2617_, v___x_2618_, v_x_2588_);
return v___x_2619_;
}
}
else
{
size_t v___x_2620_; size_t v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = lean_usize_of_nat(v___x_2613_);
lean_dec(v___x_2613_);
v___x_2621_ = lean_usize_of_nat(v___x_2614_);
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2584_, v_vs_2612_, v___x_2620_, v___x_2621_, v_x_2588_);
return v___x_2622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2623_, lean_object* v_x_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_, lean_object* v_x_2627_){
_start:
{
size_t v_x_1859__boxed_2628_; size_t v_x_1860__boxed_2629_; lean_object* v_res_2630_; 
v_x_1859__boxed_2628_ = lean_unbox_usize(v_x_2625_);
lean_dec(v_x_2625_);
v_x_1860__boxed_2629_ = lean_unbox_usize(v_x_2626_);
lean_dec(v_x_2626_);
v_res_2630_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2623_, v_x_2624_, v_x_1859__boxed_2628_, v_x_1860__boxed_2629_, v_x_2627_);
lean_dec_ref(v_x_2624_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2631_, lean_object* v_t_2632_, lean_object* v_init_2633_, lean_object* v_start_2634_){
_start:
{
lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2635_ = lean_unsigned_to_nat(0u);
v___x_2636_ = lean_nat_dec_eq(v_start_2634_, v___x_2635_);
if (v___x_2636_ == 0)
{
lean_object* v_root_2637_; lean_object* v_tail_2638_; size_t v_shift_2639_; lean_object* v_tailOff_2640_; uint8_t v___x_2641_; 
v_root_2637_ = lean_ctor_get(v_t_2632_, 0);
v_tail_2638_ = lean_ctor_get(v_t_2632_, 1);
v_shift_2639_ = lean_ctor_get_usize(v_t_2632_, 4);
v_tailOff_2640_ = lean_ctor_get(v_t_2632_, 3);
v___x_2641_ = lean_nat_dec_le(v_tailOff_2640_, v_start_2634_);
if (v___x_2641_ == 0)
{
size_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2642_ = lean_usize_of_nat(v_start_2634_);
lean_inc_ref(v_f_2631_);
v___x_2643_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2631_, v_root_2637_, v___x_2642_, v_shift_2639_, v_init_2633_);
v___x_2644_ = lean_array_get_size(v_tail_2638_);
v___x_2645_ = lean_nat_dec_lt(v___x_2635_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_dec_ref(v_f_2631_);
return v___x_2643_;
}
else
{
uint8_t v___x_2646_; 
v___x_2646_ = lean_nat_dec_le(v___x_2644_, v___x_2644_);
if (v___x_2646_ == 0)
{
if (v___x_2645_ == 0)
{
lean_dec_ref(v_f_2631_);
return v___x_2643_;
}
else
{
size_t v___x_2647_; size_t v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = ((size_t)0ULL);
v___x_2648_ = lean_usize_of_nat(v___x_2644_);
v___x_2649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2631_, v_tail_2638_, v___x_2647_, v___x_2648_, v___x_2643_);
return v___x_2649_;
}
}
else
{
size_t v___x_2650_; size_t v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = ((size_t)0ULL);
v___x_2651_ = lean_usize_of_nat(v___x_2644_);
v___x_2652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2631_, v_tail_2638_, v___x_2650_, v___x_2651_, v___x_2643_);
return v___x_2652_;
}
}
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2653_ = lean_nat_sub(v_start_2634_, v_tailOff_2640_);
v___x_2654_ = lean_array_get_size(v_tail_2638_);
v___x_2655_ = lean_nat_dec_lt(v___x_2653_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_dec(v___x_2653_);
lean_dec_ref(v_f_2631_);
return v_init_2633_;
}
else
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_nat_dec_le(v___x_2654_, v___x_2654_);
if (v___x_2656_ == 0)
{
if (v___x_2655_ == 0)
{
lean_dec(v___x_2653_);
lean_dec_ref(v_f_2631_);
return v_init_2633_;
}
else
{
size_t v___x_2657_; size_t v___x_2658_; lean_object* v___x_2659_; 
v___x_2657_ = lean_usize_of_nat(v___x_2653_);
lean_dec(v___x_2653_);
v___x_2658_ = lean_usize_of_nat(v___x_2654_);
v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2631_, v_tail_2638_, v___x_2657_, v___x_2658_, v_init_2633_);
return v___x_2659_;
}
}
else
{
size_t v___x_2660_; size_t v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_usize_of_nat(v___x_2653_);
lean_dec(v___x_2653_);
v___x_2661_ = lean_usize_of_nat(v___x_2654_);
v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2631_, v_tail_2638_, v___x_2660_, v___x_2661_, v_init_2633_);
return v___x_2662_;
}
}
}
}
else
{
lean_object* v_root_2663_; lean_object* v_tail_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v_root_2663_ = lean_ctor_get(v_t_2632_, 0);
v_tail_2664_ = lean_ctor_get(v_t_2632_, 1);
lean_inc_ref(v_f_2631_);
v___x_2665_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2631_, v_root_2663_, v_init_2633_);
v___x_2666_ = lean_array_get_size(v_tail_2664_);
v___x_2667_ = lean_nat_dec_lt(v___x_2635_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_dec_ref(v_f_2631_);
return v___x_2665_;
}
else
{
uint8_t v___x_2668_; 
v___x_2668_ = lean_nat_dec_le(v___x_2666_, v___x_2666_);
if (v___x_2668_ == 0)
{
if (v___x_2667_ == 0)
{
lean_dec_ref(v_f_2631_);
return v___x_2665_;
}
else
{
size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = ((size_t)0ULL);
v___x_2670_ = lean_usize_of_nat(v___x_2666_);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2631_, v_tail_2664_, v___x_2669_, v___x_2670_, v___x_2665_);
return v___x_2671_;
}
}
else
{
size_t v___x_2672_; size_t v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = ((size_t)0ULL);
v___x_2673_ = lean_usize_of_nat(v___x_2666_);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2631_, v_tail_2664_, v___x_2672_, v___x_2673_, v___x_2665_);
return v___x_2674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2675_, lean_object* v_t_2676_, lean_object* v_init_2677_, lean_object* v_start_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2675_, v_t_2676_, v_init_2677_, v_start_2678_);
lean_dec(v_start_2678_);
lean_dec_ref(v_t_2676_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2680_, lean_object* v_f_2681_){
_start:
{
lean_object* v_decls_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_decls_2682_ = lean_ctor_get(v_lctx_2680_, 1);
lean_inc_ref(v_decls_2682_);
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2681_, v_decls_2682_, v_lctx_2680_, v___x_2683_);
lean_dec_ref(v_decls_2682_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2685_, lean_object* v_fvarId_2686_, uint8_t v_kind_2687_){
_start:
{
lean_object* v_fvarIdToDecl_2688_; lean_object* v_decls_2689_; lean_object* v_auxDeclToFullName_2690_; lean_object* v___x_2691_; 
v_fvarIdToDecl_2688_ = lean_ctor_get(v_lctx_2685_, 0);
v_decls_2689_ = lean_ctor_get(v_lctx_2685_, 1);
v_auxDeclToFullName_2690_ = lean_ctor_get(v_lctx_2685_, 2);
lean_inc_ref(v_lctx_2685_);
v___x_2691_ = lean_local_ctx_find(v_lctx_2685_, v_fvarId_2686_);
if (lean_obj_tag(v___x_2691_) == 0)
{
return v_lctx_2685_;
}
else
{
lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2716_; 
lean_inc(v_auxDeclToFullName_2690_);
lean_inc_ref(v_decls_2689_);
lean_inc_ref(v_fvarIdToDecl_2688_);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_lctx_2685_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; lean_object* v_unused_2718_; lean_object* v_unused_2719_; 
v_unused_2717_ = lean_ctor_get(v_lctx_2685_, 2);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_lctx_2685_, 1);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_lctx_2685_, 0);
lean_dec(v_unused_2719_);
v___x_2693_ = v_lctx_2685_;
v_isShared_2694_ = v_isSharedCheck_2716_;
goto v_resetjp_2692_;
}
else
{
lean_dec(v_lctx_2685_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2716_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v_val_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2715_; 
v_val_2695_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2697_ = v___x_2691_;
v_isShared_2698_ = v_isSharedCheck_2715_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_val_2695_);
lean_dec(v___x_2691_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2715_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v_decl_2699_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2711_; lean_object* v_fvarId_2714_; 
v_decl_2699_ = l_Lean_LocalDecl_setKind(v_val_2695_, v_kind_2687_);
v_fvarId_2714_ = lean_ctor_get(v_decl_2699_, 1);
lean_inc(v_fvarId_2714_);
v___y_2711_ = v_fvarId_2714_;
goto v___jp_2710_;
v___jp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v_decl_2699_);
v___x_2704_ = v___x_2697_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_decl_2699_);
v___x_2704_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2705_ = l_Lean_PersistentArray_set___redArg(v_decls_2689_, v___y_2702_, v___x_2704_);
lean_dec(v___y_2702_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v___x_2705_);
lean_ctor_set(v___x_2693_, 0, v___y_2701_);
v___x_2707_ = v___x_2693_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___y_2701_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_auxDeclToFullName_2690_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
v___jp_2710_:
{
lean_object* v___x_2712_; lean_object* v_index_2713_; 
lean_inc_ref(v_decl_2699_);
v___x_2712_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2688_, v___y_2711_, v_decl_2699_);
v_index_2713_ = lean_ctor_get(v_decl_2699_, 0);
lean_inc(v_index_2713_);
v___y_2701_ = v___x_2712_;
v___y_2702_ = v_index_2713_;
goto v___jp_2700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2720_, lean_object* v_fvarId_2721_, lean_object* v_kind_2722_){
_start:
{
uint8_t v_kind_boxed_2723_; lean_object* v_res_2724_; 
v_kind_boxed_2723_ = lean_unbox(v_kind_2722_);
v_res_2724_ = l_Lean_LocalContext_setKind(v_lctx_2720_, v_fvarId_2721_, v_kind_boxed_2723_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2725_, lean_object* v_fvarId_2726_, uint8_t v_bi_2727_){
_start:
{
lean_object* v_fvarIdToDecl_2728_; lean_object* v_decls_2729_; lean_object* v_auxDeclToFullName_2730_; lean_object* v___x_2731_; 
v_fvarIdToDecl_2728_ = lean_ctor_get(v_lctx_2725_, 0);
v_decls_2729_ = lean_ctor_get(v_lctx_2725_, 1);
v_auxDeclToFullName_2730_ = lean_ctor_get(v_lctx_2725_, 2);
lean_inc_ref(v_lctx_2725_);
v___x_2731_ = lean_local_ctx_find(v_lctx_2725_, v_fvarId_2726_);
if (lean_obj_tag(v___x_2731_) == 0)
{
return v_lctx_2725_;
}
else
{
lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2756_; 
lean_inc(v_auxDeclToFullName_2730_);
lean_inc_ref(v_decls_2729_);
lean_inc_ref(v_fvarIdToDecl_2728_);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_lctx_2725_);
if (v_isSharedCheck_2756_ == 0)
{
lean_object* v_unused_2757_; lean_object* v_unused_2758_; lean_object* v_unused_2759_; 
v_unused_2757_ = lean_ctor_get(v_lctx_2725_, 2);
lean_dec(v_unused_2757_);
v_unused_2758_ = lean_ctor_get(v_lctx_2725_, 1);
lean_dec(v_unused_2758_);
v_unused_2759_ = lean_ctor_get(v_lctx_2725_, 0);
lean_dec(v_unused_2759_);
v___x_2733_ = v_lctx_2725_;
v_isShared_2734_ = v_isSharedCheck_2756_;
goto v_resetjp_2732_;
}
else
{
lean_dec(v_lctx_2725_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2756_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_val_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2755_; 
v_val_2735_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2737_ = v___x_2731_;
v_isShared_2738_ = v_isSharedCheck_2755_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_val_2735_);
lean_dec(v___x_2731_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2755_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v_decl_2739_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2751_; lean_object* v_fvarId_2754_; 
v_decl_2739_ = l_Lean_LocalDecl_setBinderInfo(v_val_2735_, v_bi_2727_);
v_fvarId_2754_ = lean_ctor_get(v_decl_2739_, 1);
lean_inc(v_fvarId_2754_);
v___y_2751_ = v_fvarId_2754_;
goto v___jp_2750_;
v___jp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v_decl_2739_);
v___x_2744_ = v___x_2737_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_decl_2739_);
v___x_2744_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2745_ = l_Lean_PersistentArray_set___redArg(v_decls_2729_, v___y_2742_, v___x_2744_);
lean_dec(v___y_2742_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2745_);
lean_ctor_set(v___x_2733_, 0, v___y_2741_);
v___x_2747_ = v___x_2733_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___y_2741_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_auxDeclToFullName_2730_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
v___jp_2750_:
{
lean_object* v___x_2752_; lean_object* v_index_2753_; 
lean_inc_ref(v_decl_2739_);
v___x_2752_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2728_, v___y_2751_, v_decl_2739_);
v_index_2753_ = lean_ctor_get(v_decl_2739_, 0);
lean_inc(v_index_2753_);
v___y_2741_ = v___x_2752_;
v___y_2742_ = v_index_2753_;
goto v___jp_2740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2760_, lean_object* v_fvarId_2761_, lean_object* v_bi_2762_){
_start:
{
uint8_t v_bi_boxed_2763_; lean_object* v_res_2764_; 
v_bi_boxed_2763_ = lean_unbox(v_bi_2762_);
v_res_2764_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2760_, v_fvarId_2761_, v_bi_boxed_2763_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2765_){
_start:
{
lean_object* v_decls_2766_; lean_object* v_size_2767_; 
v_decls_2766_ = lean_ctor_get(v_lctx_2765_, 1);
lean_inc_ref(v_decls_2766_);
lean_dec_ref(v_lctx_2765_);
v_size_2767_ = lean_ctor_get(v_decls_2766_, 2);
lean_inc(v_size_2767_);
lean_dec_ref(v_decls_2766_);
return v_size_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2768_, lean_object* v_i_2769_){
_start:
{
lean_object* v_decls_2770_; lean_object* v_size_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v_decls_2770_ = lean_ctor_get(v_lctx_2768_, 1);
v_size_2771_ = lean_ctor_get(v_decls_2770_, 2);
v___x_2772_ = lean_box(0);
v___x_2773_ = lean_nat_dec_lt(v_i_2769_, v_size_2771_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; 
v___x_2774_ = l_outOfBounds___redArg(v___x_2772_);
return v___x_2774_;
}
else
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2772_, v_decls_2770_, v_i_2769_);
return v___x_2775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2776_, lean_object* v_i_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2776_, v_i_2777_);
lean_dec(v_i_2777_);
lean_dec_ref(v_lctx_2776_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2779_, lean_object* v_f_2780_, lean_object* v_b_2781_, lean_object* v_decl_2782_){
_start:
{
if (lean_obj_tag(v_decl_2782_) == 0)
{
lean_object* v___x_2783_; 
lean_dec(v_f_2780_);
v___x_2783_ = lean_apply_2(v_toPure_2779_, lean_box(0), v_b_2781_);
return v___x_2783_;
}
else
{
lean_object* v_val_2784_; lean_object* v___x_2785_; 
lean_dec(v_toPure_2779_);
v_val_2784_ = lean_ctor_get(v_decl_2782_, 0);
lean_inc(v_val_2784_);
lean_dec_ref(v_decl_2782_);
v___x_2785_ = lean_apply_2(v_f_2780_, v_b_2781_, v_val_2784_);
return v___x_2785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2786_, lean_object* v_lctx_2787_, lean_object* v_f_2788_, lean_object* v_init_2789_, lean_object* v_start_2790_){
_start:
{
lean_object* v_toApplicative_2791_; lean_object* v_decls_2792_; lean_object* v_toPure_2793_; lean_object* v___f_2794_; lean_object* v___x_2795_; 
v_toApplicative_2791_ = lean_ctor_get(v_inst_2786_, 0);
v_decls_2792_ = lean_ctor_get(v_lctx_2787_, 1);
lean_inc_ref(v_decls_2792_);
lean_dec_ref(v_lctx_2787_);
v_toPure_2793_ = lean_ctor_get(v_toApplicative_2791_, 1);
lean_inc(v_toPure_2793_);
v___f_2794_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2794_, 0, v_toPure_2793_);
lean_closure_set(v___f_2794_, 1, v_f_2788_);
v___x_2795_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2786_, v_decls_2792_, v___f_2794_, v_init_2789_, v_start_2790_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2796_, lean_object* v_lctx_2797_, lean_object* v_f_2798_, lean_object* v_init_2799_, lean_object* v_start_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2796_, v_lctx_2797_, v_f_2798_, v_init_2799_, v_start_2800_);
lean_dec(v_start_2800_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2802_, lean_object* v_00_u03b2_2803_, lean_object* v_inst_2804_, lean_object* v_lctx_2805_, lean_object* v_f_2806_, lean_object* v_init_2807_, lean_object* v_start_2808_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2804_, v_lctx_2805_, v_f_2806_, v_init_2807_, v_start_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2810_, lean_object* v_00_u03b2_2811_, lean_object* v_inst_2812_, lean_object* v_lctx_2813_, lean_object* v_f_2814_, lean_object* v_init_2815_, lean_object* v_start_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_LocalContext_foldlM(v_m_2810_, v_00_u03b2_2811_, v_inst_2812_, v_lctx_2813_, v_f_2814_, v_init_2815_, v_start_2816_);
lean_dec(v_start_2816_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2818_, lean_object* v_f_2819_, lean_object* v_decl_2820_, lean_object* v_b_2821_){
_start:
{
if (lean_obj_tag(v_decl_2820_) == 0)
{
lean_object* v___x_2822_; 
lean_dec(v_f_2819_);
v___x_2822_ = lean_apply_2(v_toPure_2818_, lean_box(0), v_b_2821_);
return v___x_2822_;
}
else
{
lean_object* v_val_2823_; lean_object* v___x_2824_; 
lean_dec(v_toPure_2818_);
v_val_2823_ = lean_ctor_get(v_decl_2820_, 0);
lean_inc(v_val_2823_);
lean_dec_ref(v_decl_2820_);
v___x_2824_ = lean_apply_2(v_f_2819_, v_val_2823_, v_b_2821_);
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2825_, lean_object* v_lctx_2826_, lean_object* v_f_2827_, lean_object* v_init_2828_){
_start:
{
lean_object* v_toApplicative_2829_; lean_object* v_decls_2830_; lean_object* v_toPure_2831_; lean_object* v___f_2832_; lean_object* v___x_2833_; 
v_toApplicative_2829_ = lean_ctor_get(v_inst_2825_, 0);
v_decls_2830_ = lean_ctor_get(v_lctx_2826_, 1);
lean_inc_ref(v_decls_2830_);
lean_dec_ref(v_lctx_2826_);
v_toPure_2831_ = lean_ctor_get(v_toApplicative_2829_, 1);
lean_inc(v_toPure_2831_);
v___f_2832_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2832_, 0, v_toPure_2831_);
lean_closure_set(v___f_2832_, 1, v_f_2827_);
v___x_2833_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2825_, v_decls_2830_, v___f_2832_, v_init_2828_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2834_, lean_object* v_00_u03b2_2835_, lean_object* v_inst_2836_, lean_object* v_lctx_2837_, lean_object* v_f_2838_, lean_object* v_init_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2836_, v_lctx_2837_, v_f_2838_, v_init_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2841_, lean_object* v_f_2842_, lean_object* v_decl_2843_){
_start:
{
if (lean_obj_tag(v_decl_2843_) == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_dec(v_f_2842_);
v___x_2844_ = lean_box(0);
v___x_2845_ = lean_apply_2(v_toPure_2841_, lean_box(0), v___x_2844_);
return v___x_2845_;
}
else
{
lean_object* v_val_2846_; lean_object* v___x_2847_; 
lean_dec(v_toPure_2841_);
v_val_2846_ = lean_ctor_get(v_decl_2843_, 0);
lean_inc(v_val_2846_);
lean_dec_ref(v_decl_2843_);
v___x_2847_ = lean_apply_1(v_f_2842_, v_val_2846_);
return v___x_2847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2848_, lean_object* v_lctx_2849_, lean_object* v_f_2850_, lean_object* v_start_2851_){
_start:
{
lean_object* v_toApplicative_2852_; lean_object* v_decls_2853_; lean_object* v_toPure_2854_; lean_object* v___f_2855_; lean_object* v___x_2856_; 
v_toApplicative_2852_ = lean_ctor_get(v_inst_2848_, 0);
v_decls_2853_ = lean_ctor_get(v_lctx_2849_, 1);
lean_inc_ref(v_decls_2853_);
lean_dec_ref(v_lctx_2849_);
v_toPure_2854_ = lean_ctor_get(v_toApplicative_2852_, 1);
lean_inc(v_toPure_2854_);
v___f_2855_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2855_, 0, v_toPure_2854_);
lean_closure_set(v___f_2855_, 1, v_f_2850_);
v___x_2856_ = l_Lean_PersistentArray_forM___redArg(v_inst_2848_, v_decls_2853_, v___f_2855_, v_start_2851_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2857_, lean_object* v_lctx_2858_, lean_object* v_f_2859_, lean_object* v_start_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_LocalContext_forM___redArg(v_inst_2857_, v_lctx_2858_, v_f_2859_, v_start_2860_);
lean_dec(v_start_2860_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2862_, lean_object* v_inst_2863_, lean_object* v_lctx_2864_, lean_object* v_f_2865_, lean_object* v_start_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_LocalContext_forM___redArg(v_inst_2863_, v_lctx_2864_, v_f_2865_, v_start_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2868_, lean_object* v_inst_2869_, lean_object* v_lctx_2870_, lean_object* v_f_2871_, lean_object* v_start_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_LocalContext_forM(v_m_2868_, v_inst_2869_, v_lctx_2870_, v_f_2871_, v_start_2872_);
lean_dec(v_start_2872_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2874_, lean_object* v_f_2875_, lean_object* v_decl_2876_){
_start:
{
if (lean_obj_tag(v_decl_2876_) == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
lean_dec(v_f_2875_);
v___x_2877_ = lean_box(0);
v___x_2878_ = lean_apply_2(v_toPure_2874_, lean_box(0), v___x_2877_);
return v___x_2878_;
}
else
{
lean_object* v_val_2879_; lean_object* v___x_2880_; 
lean_dec(v_toPure_2874_);
v_val_2879_ = lean_ctor_get(v_decl_2876_, 0);
lean_inc(v_val_2879_);
lean_dec_ref(v_decl_2876_);
v___x_2880_ = lean_apply_1(v_f_2875_, v_val_2879_);
return v___x_2880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2881_, lean_object* v_lctx_2882_, lean_object* v_f_2883_){
_start:
{
lean_object* v_toApplicative_2884_; lean_object* v_decls_2885_; lean_object* v_toPure_2886_; lean_object* v___f_2887_; lean_object* v___x_2888_; 
v_toApplicative_2884_ = lean_ctor_get(v_inst_2881_, 0);
v_decls_2885_ = lean_ctor_get(v_lctx_2882_, 1);
lean_inc_ref(v_decls_2885_);
lean_dec_ref(v_lctx_2882_);
v_toPure_2886_ = lean_ctor_get(v_toApplicative_2884_, 1);
lean_inc(v_toPure_2886_);
v___f_2887_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2887_, 0, v_toPure_2886_);
lean_closure_set(v___f_2887_, 1, v_f_2883_);
v___x_2888_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2881_, v_decls_2885_, v___f_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2889_, lean_object* v_00_u03b2_2890_, lean_object* v_inst_2891_, lean_object* v_lctx_2892_, lean_object* v_f_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2891_, v_lctx_2892_, v_f_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2895_, lean_object* v_lctx_2896_, lean_object* v_f_2897_){
_start:
{
lean_object* v_toApplicative_2898_; lean_object* v_decls_2899_; lean_object* v_toPure_2900_; lean_object* v___f_2901_; lean_object* v___x_2902_; 
v_toApplicative_2898_ = lean_ctor_get(v_inst_2895_, 0);
v_decls_2899_ = lean_ctor_get(v_lctx_2896_, 1);
lean_inc_ref(v_decls_2899_);
lean_dec_ref(v_lctx_2896_);
v_toPure_2900_ = lean_ctor_get(v_toApplicative_2898_, 1);
lean_inc(v_toPure_2900_);
v___f_2901_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2901_, 0, v_toPure_2900_);
lean_closure_set(v___f_2901_, 1, v_f_2897_);
v___x_2902_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2895_, v_decls_2899_, v___f_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2903_, lean_object* v_00_u03b2_2904_, lean_object* v_inst_2905_, lean_object* v_lctx_2906_, lean_object* v_f_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2905_, v_lctx_2906_, v_f_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2909_, lean_object* v_f_2910_, lean_object* v_d_x3f_2911_, lean_object* v_b_2912_){
_start:
{
if (lean_obj_tag(v_d_x3f_2911_) == 0)
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
lean_dec(v_f_2910_);
v___x_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2913_, 0, v_b_2912_);
v___x_2914_ = lean_apply_2(v_toPure_2909_, lean_box(0), v___x_2913_);
return v___x_2914_;
}
else
{
lean_object* v_val_2915_; lean_object* v___x_2916_; 
lean_dec(v_toPure_2909_);
v_val_2915_ = lean_ctor_get(v_d_x3f_2911_, 0);
lean_inc(v_val_2915_);
lean_dec_ref(v_d_x3f_2911_);
v___x_2916_ = lean_apply_2(v_f_2910_, v_val_2915_, v_b_2912_);
return v___x_2916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2917_, lean_object* v_inst_2918_, lean_object* v_00_u03b2_2919_, lean_object* v_lctx_2920_, lean_object* v_init_2921_, lean_object* v_f_2922_){
_start:
{
lean_object* v_decls_2923_; lean_object* v___f_2924_; lean_object* v___x_2925_; 
v_decls_2923_ = lean_ctor_get(v_lctx_2920_, 1);
v___f_2924_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2924_, 0, v_toPure_2917_);
lean_closure_set(v___f_2924_, 1, v_f_2922_);
v___x_2925_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2918_, v_decls_2923_, v_init_2921_, v___f_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object* v_toPure_2926_, lean_object* v_inst_2927_, lean_object* v_00_u03b2_2928_, lean_object* v_lctx_2929_, lean_object* v_init_2930_, lean_object* v_f_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(v_toPure_2926_, v_inst_2927_, v_00_u03b2_2928_, v_lctx_2929_, v_init_2930_, v_f_2931_);
lean_dec_ref(v_lctx_2929_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2933_){
_start:
{
lean_object* v_toApplicative_2934_; lean_object* v_toPure_2935_; lean_object* v___f_2936_; 
v_toApplicative_2934_ = lean_ctor_get(v_inst_2933_, 0);
v_toPure_2935_ = lean_ctor_get(v_toApplicative_2934_, 1);
lean_inc(v_toPure_2935_);
v___f_2936_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2936_, 0, v_toPure_2935_);
lean_closure_set(v___f_2936_, 1, v_inst_2933_);
return v___f_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2937_, lean_object* v_inst_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2940_, lean_object* v_x1_2941_, lean_object* v_x2_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_apply_2(v_f_2940_, v_x1_2941_, v_x2_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2963_, lean_object* v_f_2964_, lean_object* v_init_2965_, lean_object* v_start_2966_){
_start:
{
lean_object* v___f_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___f_2967_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2967_, 0, v_f_2964_);
v___x_2968_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2969_ = l_Lean_LocalContext_foldlM___redArg(v___x_2968_, v_lctx_2963_, v___f_2967_, v_init_2965_, v_start_2966_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_2970_, lean_object* v_f_2971_, lean_object* v_init_2972_, lean_object* v_start_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_LocalContext_foldl___redArg(v_lctx_2970_, v_f_2971_, v_init_2972_, v_start_2973_);
lean_dec(v_start_2973_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_2975_, lean_object* v_lctx_2976_, lean_object* v_f_2977_, lean_object* v_init_2978_, lean_object* v_start_2979_){
_start:
{
lean_object* v___f_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___f_2980_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2980_, 0, v_f_2977_);
v___x_2981_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2982_ = l_Lean_LocalContext_foldlM___redArg(v___x_2981_, v_lctx_2976_, v___f_2980_, v_init_2978_, v_start_2979_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_2983_, lean_object* v_lctx_2984_, lean_object* v_f_2985_, lean_object* v_init_2986_, lean_object* v_start_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Lean_LocalContext_foldl(v_00_u03b2_2983_, v_lctx_2984_, v_f_2985_, v_init_2986_, v_start_2987_);
lean_dec(v_start_2987_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_2989_, lean_object* v_x1_2990_, lean_object* v_x2_2991_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_apply_2(v_f_2989_, v_x1_2990_, v_x2_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_2993_, lean_object* v_f_2994_, lean_object* v_init_2995_){
_start:
{
lean_object* v___f_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___f_2996_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2996_, 0, v_f_2994_);
v___x_2997_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2998_ = l_Lean_LocalContext_foldrM___redArg(v___x_2997_, v_lctx_2993_, v___f_2996_, v_init_2995_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_2999_, lean_object* v_lctx_3000_, lean_object* v_f_3001_, lean_object* v_init_3002_){
_start:
{
lean_object* v___f_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___f_3003_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3003_, 0, v_f_3001_);
v___x_3004_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3005_ = l_Lean_LocalContext_foldrM___redArg(v___x_3004_, v_lctx_3000_, v___f_3003_, v_init_3002_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_3006_, size_t v_i_3007_, size_t v_stop_3008_, lean_object* v_b_3009_){
_start:
{
lean_object* v___y_3011_; uint8_t v___x_3015_; 
v___x_3015_ = lean_usize_dec_eq(v_i_3007_, v_stop_3008_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_array_uget_borrowed(v_as_3006_, v_i_3007_);
if (lean_obj_tag(v___x_3016_) == 0)
{
v___y_3011_ = v_b_3009_;
goto v___jp_3010_;
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_unsigned_to_nat(1u);
v___x_3018_ = lean_nat_add(v_b_3009_, v___x_3017_);
lean_dec(v_b_3009_);
v___y_3011_ = v___x_3018_;
goto v___jp_3010_;
}
}
else
{
return v_b_3009_;
}
v___jp_3010_:
{
size_t v___x_3012_; size_t v___x_3013_; 
v___x_3012_ = ((size_t)1ULL);
v___x_3013_ = lean_usize_add(v_i_3007_, v___x_3012_);
v_i_3007_ = v___x_3013_;
v_b_3009_ = v___y_3011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3019_, lean_object* v_i_3020_, lean_object* v_stop_3021_, lean_object* v_b_3022_){
_start:
{
size_t v_i_boxed_3023_; size_t v_stop_boxed_3024_; lean_object* v_res_3025_; 
v_i_boxed_3023_ = lean_unbox_usize(v_i_3020_);
lean_dec(v_i_3020_);
v_stop_boxed_3024_ = lean_unbox_usize(v_stop_3021_);
lean_dec(v_stop_3021_);
v_res_3025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_3019_, v_i_boxed_3023_, v_stop_boxed_3024_, v_b_3022_);
lean_dec_ref(v_as_3019_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3026_, lean_object* v_x_3027_){
_start:
{
if (lean_obj_tag(v_x_3026_) == 0)
{
lean_object* v_cs_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v_cs_3028_ = lean_ctor_get(v_x_3026_, 0);
v___x_3029_ = lean_unsigned_to_nat(0u);
v___x_3030_ = lean_array_get_size(v_cs_3028_);
v___x_3031_ = lean_nat_dec_lt(v___x_3029_, v___x_3030_);
if (v___x_3031_ == 0)
{
return v_x_3027_;
}
else
{
uint8_t v___x_3032_; 
v___x_3032_ = lean_nat_dec_le(v___x_3030_, v___x_3030_);
if (v___x_3032_ == 0)
{
if (v___x_3031_ == 0)
{
return v_x_3027_;
}
else
{
size_t v___x_3033_; size_t v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = ((size_t)0ULL);
v___x_3034_ = lean_usize_of_nat(v___x_3030_);
v___x_3035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3028_, v___x_3033_, v___x_3034_, v_x_3027_);
return v___x_3035_;
}
}
else
{
size_t v___x_3036_; size_t v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = ((size_t)0ULL);
v___x_3037_ = lean_usize_of_nat(v___x_3030_);
v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3028_, v___x_3036_, v___x_3037_, v_x_3027_);
return v___x_3038_;
}
}
}
else
{
lean_object* v_vs_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v_vs_3039_ = lean_ctor_get(v_x_3026_, 0);
v___x_3040_ = lean_unsigned_to_nat(0u);
v___x_3041_ = lean_array_get_size(v_vs_3039_);
v___x_3042_ = lean_nat_dec_lt(v___x_3040_, v___x_3041_);
if (v___x_3042_ == 0)
{
return v_x_3027_;
}
else
{
uint8_t v___x_3043_; 
v___x_3043_ = lean_nat_dec_le(v___x_3041_, v___x_3041_);
if (v___x_3043_ == 0)
{
if (v___x_3042_ == 0)
{
return v_x_3027_;
}
else
{
size_t v___x_3044_; size_t v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = ((size_t)0ULL);
v___x_3045_ = lean_usize_of_nat(v___x_3041_);
v___x_3046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3039_, v___x_3044_, v___x_3045_, v_x_3027_);
return v___x_3046_;
}
}
else
{
size_t v___x_3047_; size_t v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = ((size_t)0ULL);
v___x_3048_ = lean_usize_of_nat(v___x_3041_);
v___x_3049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3039_, v___x_3047_, v___x_3048_, v_x_3027_);
return v___x_3049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3050_, size_t v_i_3051_, size_t v_stop_3052_, lean_object* v_b_3053_){
_start:
{
uint8_t v___x_3054_; 
v___x_3054_ = lean_usize_dec_eq(v_i_3051_, v_stop_3052_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; size_t v___x_3057_; size_t v___x_3058_; 
v___x_3055_ = lean_array_uget_borrowed(v_as_3050_, v_i_3051_);
v___x_3056_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3055_, v_b_3053_);
v___x_3057_ = ((size_t)1ULL);
v___x_3058_ = lean_usize_add(v_i_3051_, v___x_3057_);
v_i_3051_ = v___x_3058_;
v_b_3053_ = v___x_3056_;
goto _start;
}
else
{
return v_b_3053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3060_, lean_object* v_i_3061_, lean_object* v_stop_3062_, lean_object* v_b_3063_){
_start:
{
size_t v_i_boxed_3064_; size_t v_stop_boxed_3065_; lean_object* v_res_3066_; 
v_i_boxed_3064_ = lean_unbox_usize(v_i_3061_);
lean_dec(v_i_3061_);
v_stop_boxed_3065_ = lean_unbox_usize(v_stop_3062_);
lean_dec(v_stop_3062_);
v_res_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3060_, v_i_boxed_3064_, v_stop_boxed_3065_, v_b_3063_);
lean_dec_ref(v_as_3060_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3067_, lean_object* v_x_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3067_, v_x_3068_);
lean_dec_ref(v_x_3067_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3070_, size_t v_x_3071_, size_t v_x_3072_, lean_object* v_x_3073_){
_start:
{
if (lean_obj_tag(v_x_3070_) == 0)
{
lean_object* v_cs_3074_; lean_object* v___x_3075_; size_t v___x_3076_; lean_object* v_j_3077_; lean_object* v___x_3078_; size_t v___x_3079_; size_t v___x_3080_; size_t v___x_3081_; size_t v___x_3082_; size_t v___x_3083_; size_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v_cs_3074_ = lean_ctor_get(v_x_3070_, 0);
v___x_3075_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3076_ = lean_usize_shift_right(v_x_3071_, v_x_3072_);
v_j_3077_ = lean_usize_to_nat(v___x_3076_);
v___x_3078_ = lean_array_get_borrowed(v___x_3075_, v_cs_3074_, v_j_3077_);
v___x_3079_ = ((size_t)1ULL);
v___x_3080_ = lean_usize_shift_left(v___x_3079_, v_x_3072_);
v___x_3081_ = lean_usize_sub(v___x_3080_, v___x_3079_);
v___x_3082_ = lean_usize_land(v_x_3071_, v___x_3081_);
v___x_3083_ = ((size_t)5ULL);
v___x_3084_ = lean_usize_sub(v_x_3072_, v___x_3083_);
v___x_3085_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3078_, v___x_3082_, v___x_3084_, v_x_3073_);
v___x_3086_ = lean_unsigned_to_nat(1u);
v___x_3087_ = lean_nat_add(v_j_3077_, v___x_3086_);
lean_dec(v_j_3077_);
v___x_3088_ = lean_array_get_size(v_cs_3074_);
v___x_3089_ = lean_nat_dec_lt(v___x_3087_, v___x_3088_);
if (v___x_3089_ == 0)
{
lean_dec(v___x_3087_);
return v___x_3085_;
}
else
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_nat_dec_le(v___x_3088_, v___x_3088_);
if (v___x_3090_ == 0)
{
if (v___x_3089_ == 0)
{
lean_dec(v___x_3087_);
return v___x_3085_;
}
else
{
size_t v___x_3091_; size_t v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = lean_usize_of_nat(v___x_3087_);
lean_dec(v___x_3087_);
v___x_3092_ = lean_usize_of_nat(v___x_3088_);
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3074_, v___x_3091_, v___x_3092_, v___x_3085_);
return v___x_3093_;
}
}
else
{
size_t v___x_3094_; size_t v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = lean_usize_of_nat(v___x_3087_);
lean_dec(v___x_3087_);
v___x_3095_ = lean_usize_of_nat(v___x_3088_);
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3074_, v___x_3094_, v___x_3095_, v___x_3085_);
return v___x_3096_;
}
}
}
else
{
lean_object* v_vs_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v_vs_3097_ = lean_ctor_get(v_x_3070_, 0);
v___x_3098_ = lean_usize_to_nat(v_x_3071_);
v___x_3099_ = lean_array_get_size(v_vs_3097_);
v___x_3100_ = lean_nat_dec_lt(v___x_3098_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_dec(v___x_3098_);
return v_x_3073_;
}
else
{
uint8_t v___x_3101_; 
v___x_3101_ = lean_nat_dec_le(v___x_3099_, v___x_3099_);
if (v___x_3101_ == 0)
{
if (v___x_3100_ == 0)
{
lean_dec(v___x_3098_);
return v_x_3073_;
}
else
{
size_t v___x_3102_; size_t v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = lean_usize_of_nat(v___x_3098_);
lean_dec(v___x_3098_);
v___x_3103_ = lean_usize_of_nat(v___x_3099_);
v___x_3104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3097_, v___x_3102_, v___x_3103_, v_x_3073_);
return v___x_3104_;
}
}
else
{
size_t v___x_3105_; size_t v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = lean_usize_of_nat(v___x_3098_);
lean_dec(v___x_3098_);
v___x_3106_ = lean_usize_of_nat(v___x_3099_);
v___x_3107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3097_, v___x_3105_, v___x_3106_, v_x_3073_);
return v___x_3107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3108_, lean_object* v_x_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_){
_start:
{
size_t v_x_1557__boxed_3112_; size_t v_x_1558__boxed_3113_; lean_object* v_res_3114_; 
v_x_1557__boxed_3112_ = lean_unbox_usize(v_x_3109_);
lean_dec(v_x_3109_);
v_x_1558__boxed_3113_ = lean_unbox_usize(v_x_3110_);
lean_dec(v_x_3110_);
v_res_3114_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3108_, v_x_1557__boxed_3112_, v_x_1558__boxed_3113_, v_x_3111_);
lean_dec_ref(v_x_3108_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3115_, lean_object* v_init_3116_, lean_object* v_start_3117_){
_start:
{
lean_object* v___x_3118_; uint8_t v___x_3119_; 
v___x_3118_ = lean_unsigned_to_nat(0u);
v___x_3119_ = lean_nat_dec_eq(v_start_3117_, v___x_3118_);
if (v___x_3119_ == 0)
{
lean_object* v_root_3120_; lean_object* v_tail_3121_; size_t v_shift_3122_; lean_object* v_tailOff_3123_; uint8_t v___x_3124_; 
v_root_3120_ = lean_ctor_get(v_t_3115_, 0);
v_tail_3121_ = lean_ctor_get(v_t_3115_, 1);
v_shift_3122_ = lean_ctor_get_usize(v_t_3115_, 4);
v_tailOff_3123_ = lean_ctor_get(v_t_3115_, 3);
v___x_3124_ = lean_nat_dec_le(v_tailOff_3123_, v_start_3117_);
if (v___x_3124_ == 0)
{
size_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3125_ = lean_usize_of_nat(v_start_3117_);
v___x_3126_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3120_, v___x_3125_, v_shift_3122_, v_init_3116_);
v___x_3127_ = lean_array_get_size(v_tail_3121_);
v___x_3128_ = lean_nat_dec_lt(v___x_3118_, v___x_3127_);
if (v___x_3128_ == 0)
{
return v___x_3126_;
}
else
{
uint8_t v___x_3129_; 
v___x_3129_ = lean_nat_dec_le(v___x_3127_, v___x_3127_);
if (v___x_3129_ == 0)
{
if (v___x_3128_ == 0)
{
return v___x_3126_;
}
else
{
size_t v___x_3130_; size_t v___x_3131_; lean_object* v___x_3132_; 
v___x_3130_ = ((size_t)0ULL);
v___x_3131_ = lean_usize_of_nat(v___x_3127_);
v___x_3132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3121_, v___x_3130_, v___x_3131_, v___x_3126_);
return v___x_3132_;
}
}
else
{
size_t v___x_3133_; size_t v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = ((size_t)0ULL);
v___x_3134_ = lean_usize_of_nat(v___x_3127_);
v___x_3135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3121_, v___x_3133_, v___x_3134_, v___x_3126_);
return v___x_3135_;
}
}
}
else
{
lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3136_ = lean_nat_sub(v_start_3117_, v_tailOff_3123_);
v___x_3137_ = lean_array_get_size(v_tail_3121_);
v___x_3138_ = lean_nat_dec_lt(v___x_3136_, v___x_3137_);
if (v___x_3138_ == 0)
{
lean_dec(v___x_3136_);
return v_init_3116_;
}
else
{
uint8_t v___x_3139_; 
v___x_3139_ = lean_nat_dec_le(v___x_3137_, v___x_3137_);
if (v___x_3139_ == 0)
{
if (v___x_3138_ == 0)
{
lean_dec(v___x_3136_);
return v_init_3116_;
}
else
{
size_t v___x_3140_; size_t v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = lean_usize_of_nat(v___x_3136_);
lean_dec(v___x_3136_);
v___x_3141_ = lean_usize_of_nat(v___x_3137_);
v___x_3142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3121_, v___x_3140_, v___x_3141_, v_init_3116_);
return v___x_3142_;
}
}
else
{
size_t v___x_3143_; size_t v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = lean_usize_of_nat(v___x_3136_);
lean_dec(v___x_3136_);
v___x_3144_ = lean_usize_of_nat(v___x_3137_);
v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3121_, v___x_3143_, v___x_3144_, v_init_3116_);
return v___x_3145_;
}
}
}
}
else
{
lean_object* v_root_3146_; lean_object* v_tail_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v_root_3146_ = lean_ctor_get(v_t_3115_, 0);
v_tail_3147_ = lean_ctor_get(v_t_3115_, 1);
v___x_3148_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3146_, v_init_3116_);
v___x_3149_ = lean_array_get_size(v_tail_3147_);
v___x_3150_ = lean_nat_dec_lt(v___x_3118_, v___x_3149_);
if (v___x_3150_ == 0)
{
return v___x_3148_;
}
else
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_nat_dec_le(v___x_3149_, v___x_3149_);
if (v___x_3151_ == 0)
{
if (v___x_3150_ == 0)
{
return v___x_3148_;
}
else
{
size_t v___x_3152_; size_t v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = ((size_t)0ULL);
v___x_3153_ = lean_usize_of_nat(v___x_3149_);
v___x_3154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3147_, v___x_3152_, v___x_3153_, v___x_3148_);
return v___x_3154_;
}
}
else
{
size_t v___x_3155_; size_t v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = ((size_t)0ULL);
v___x_3156_ = lean_usize_of_nat(v___x_3149_);
v___x_3157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3147_, v___x_3155_, v___x_3156_, v___x_3148_);
return v___x_3157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3158_, lean_object* v_init_3159_, lean_object* v_start_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3158_, v_init_3159_, v_start_3160_);
lean_dec(v_start_3160_);
lean_dec_ref(v_t_3158_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3162_, lean_object* v_init_3163_, lean_object* v_start_3164_){
_start:
{
lean_object* v_decls_3165_; lean_object* v___x_3166_; 
v_decls_3165_ = lean_ctor_get(v_lctx_3162_, 1);
v___x_3166_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3165_, v_init_3163_, v_start_3164_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3167_, lean_object* v_init_3168_, lean_object* v_start_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3167_, v_init_3168_, v_start_3169_);
lean_dec(v_start_3169_);
lean_dec_ref(v_lctx_3167_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3171_){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_unsigned_to_nat(0u);
v___x_3173_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3171_, v___x_3172_, v___x_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Lean_LocalContext_size(v_lctx_3174_);
lean_dec_ref(v_lctx_3174_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3176_, lean_object* v_x_3177_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = lean_apply_1(v_f_3176_, v_x_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3179_, lean_object* v_f_3180_){
_start:
{
lean_object* v___f_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___f_3181_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3181_, 0, v_f_3180_);
v___x_3182_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3183_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3182_, v_lctx_3179_, v___f_3181_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3184_, lean_object* v_lctx_3185_, lean_object* v_f_3186_){
_start:
{
lean_object* v___f_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___f_3187_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3187_, 0, v_f_3186_);
v___x_3188_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3189_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3188_, v_lctx_3185_, v___f_3187_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3190_, lean_object* v_f_3191_){
_start:
{
lean_object* v___f_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___f_3192_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3192_, 0, v_f_3191_);
v___x_3193_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3194_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3193_, v_lctx_3190_, v___f_3192_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3195_, lean_object* v_lctx_3196_, lean_object* v_f_3197_){
_start:
{
lean_object* v___f_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___f_3198_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3198_, 0, v_f_3197_);
v___x_3199_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3200_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3199_, v_lctx_3196_, v___f_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3201_, lean_object* v_as_3202_, size_t v_i_3203_, size_t v_stop_3204_){
_start:
{
uint8_t v___x_3205_; 
v___x_3205_ = lean_usize_dec_eq(v_i_3203_, v_stop_3204_);
if (v___x_3205_ == 0)
{
uint8_t v___x_3206_; uint8_t v___y_3208_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v_fvarId_3214_; uint8_t v___x_3215_; 
v___x_3206_ = 1;
v___x_3212_ = lean_array_uget_borrowed(v_as_3202_, v_i_3203_);
v___x_3213_ = l_Lean_Expr_fvarId_x21(v___x_3212_);
v_fvarId_3214_ = lean_ctor_get(v_val_3201_, 1);
v___x_3215_ = l_Lean_instBEqFVarId_beq(v___x_3213_, v_fvarId_3214_);
lean_dec(v___x_3213_);
v___y_3208_ = v___x_3215_;
goto v___jp_3207_;
v___jp_3207_:
{
if (v___y_3208_ == 0)
{
size_t v___x_3209_; size_t v___x_3210_; 
v___x_3209_ = ((size_t)1ULL);
v___x_3210_ = lean_usize_add(v_i_3203_, v___x_3209_);
v_i_3203_ = v___x_3210_;
goto _start;
}
else
{
return v___x_3206_;
}
}
}
else
{
uint8_t v___x_3216_; 
v___x_3216_ = 0;
return v___x_3216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3217_, lean_object* v_as_3218_, lean_object* v_i_3219_, lean_object* v_stop_3220_){
_start:
{
size_t v_i_boxed_3221_; size_t v_stop_boxed_3222_; uint8_t v_res_3223_; lean_object* v_r_3224_; 
v_i_boxed_3221_ = lean_unbox_usize(v_i_3219_);
lean_dec(v_i_3219_);
v_stop_boxed_3222_ = lean_unbox_usize(v_stop_3220_);
lean_dec(v_stop_3220_);
v_res_3223_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3217_, v_as_3218_, v_i_boxed_3221_, v_stop_boxed_3222_);
lean_dec_ref(v_as_3218_);
lean_dec_ref(v_val_3217_);
v_r_3224_ = lean_box(v_res_3223_);
return v_r_3224_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3225_, lean_object* v_a_u2082_3226_, lean_object* v_exceptFVars_3227_, lean_object* v_i_3228_, lean_object* v_j_3229_){
_start:
{
lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v_size_3245_; uint8_t v___x_3246_; 
v_size_3245_ = lean_ctor_get(v_a_u2081_3225_, 2);
v___x_3246_ = lean_nat_dec_lt(v_i_3228_, v_size_3245_);
if (v___x_3246_ == 0)
{
uint8_t v___x_3247_; 
lean_dec(v_j_3229_);
lean_dec(v_i_3228_);
v___x_3247_ = 1;
return v___x_3247_;
}
else
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = lean_box(0);
v___x_3249_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3248_, v_a_u2081_3225_, v_i_3228_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = lean_unsigned_to_nat(1u);
v___x_3251_ = lean_nat_add(v_i_3228_, v___x_3250_);
lean_dec(v_i_3228_);
v_i_3228_ = v___x_3251_;
goto _start;
}
else
{
lean_object* v_val_3253_; uint8_t v___y_3255_; lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v_val_3253_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_val_3253_);
lean_dec_ref(v___x_3249_);
v___x_3264_ = lean_unsigned_to_nat(0u);
v___x_3265_ = lean_array_get_size(v_exceptFVars_3227_);
v___x_3266_ = lean_nat_dec_lt(v___x_3264_, v___x_3265_);
if (v___x_3266_ == 0)
{
v___y_3255_ = v___x_3266_;
goto v___jp_3254_;
}
else
{
if (v___x_3266_ == 0)
{
v___y_3255_ = v___x_3266_;
goto v___jp_3254_;
}
else
{
size_t v___x_3267_; size_t v___x_3268_; uint8_t v___x_3269_; 
v___x_3267_ = ((size_t)0ULL);
v___x_3268_ = lean_usize_of_nat(v___x_3265_);
v___x_3269_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3253_, v_exceptFVars_3227_, v___x_3267_, v___x_3268_);
if (v___x_3269_ == 0)
{
v___y_3255_ = v___x_3269_;
goto v___jp_3254_;
}
else
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_dec(v_val_3253_);
v___x_3270_ = lean_unsigned_to_nat(1u);
v___x_3271_ = lean_nat_add(v_i_3228_, v___x_3270_);
lean_dec(v_i_3228_);
v_i_3228_ = v___x_3271_;
goto _start;
}
}
}
v___jp_3254_:
{
lean_object* v_size_3256_; uint8_t v___x_3257_; 
v_size_3256_ = lean_ctor_get(v_a_u2082_3226_, 2);
v___x_3257_ = lean_nat_dec_lt(v_j_3229_, v_size_3256_);
if (v___x_3257_ == 0)
{
lean_dec(v_val_3253_);
lean_dec(v_j_3229_);
lean_dec(v_i_3228_);
return v___y_3255_;
}
else
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3248_, v_a_u2082_3226_, v_j_3229_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_dec(v_val_3253_);
v___x_3259_ = lean_unsigned_to_nat(1u);
v___x_3260_ = lean_nat_add(v_j_3229_, v___x_3259_);
lean_dec(v_j_3229_);
v_j_3229_ = v___x_3260_;
goto _start;
}
else
{
lean_object* v_val_3262_; lean_object* v_fvarId_3263_; 
v_val_3262_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_val_3262_);
lean_dec_ref(v___x_3258_);
v_fvarId_3263_ = lean_ctor_get(v_val_3253_, 1);
lean_inc(v_fvarId_3263_);
lean_dec(v_val_3253_);
v___y_3242_ = v_val_3262_;
v___y_3243_ = v_fvarId_3263_;
goto v___jp_3241_;
}
}
}
}
}
v___jp_3230_:
{
uint8_t v___x_3233_; 
v___x_3233_ = l_Lean_instBEqFVarId_beq(v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec(v___y_3231_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = lean_unsigned_to_nat(1u);
v___x_3235_ = lean_nat_add(v_j_3229_, v___x_3234_);
lean_dec(v_j_3229_);
v_j_3229_ = v___x_3235_;
goto _start;
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_unsigned_to_nat(1u);
v___x_3238_ = lean_nat_add(v_i_3228_, v___x_3237_);
lean_dec(v_i_3228_);
v___x_3239_ = lean_nat_add(v_j_3229_, v___x_3237_);
lean_dec(v_j_3229_);
v_i_3228_ = v___x_3238_;
v_j_3229_ = v___x_3239_;
goto _start;
}
}
v___jp_3241_:
{
lean_object* v_fvarId_3244_; 
v_fvarId_3244_ = lean_ctor_get(v___y_3242_, 1);
lean_inc(v_fvarId_3244_);
lean_dec_ref(v___y_3242_);
v___y_3231_ = v___y_3243_;
v___y_3232_ = v_fvarId_3244_;
goto v___jp_3230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3273_, lean_object* v_a_u2082_3274_, lean_object* v_exceptFVars_3275_, lean_object* v_i_3276_, lean_object* v_j_3277_){
_start:
{
uint8_t v_res_3278_; lean_object* v_r_3279_; 
v_res_3278_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3273_, v_a_u2082_3274_, v_exceptFVars_3275_, v_i_3276_, v_j_3277_);
lean_dec_ref(v_exceptFVars_3275_);
lean_dec_ref(v_a_u2082_3274_);
lean_dec_ref(v_a_u2081_3273_);
v_r_3279_ = lean_box(v_res_3278_);
return v_r_3279_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3280_, lean_object* v_lctx_u2082_3281_, lean_object* v_exceptFVars_3282_){
_start:
{
lean_object* v_decls_3283_; lean_object* v_decls_3284_; lean_object* v___x_3285_; uint8_t v___x_3286_; 
v_decls_3283_ = lean_ctor_get(v_lctx_u2081_3280_, 1);
v_decls_3284_ = lean_ctor_get(v_lctx_u2082_3281_, 1);
v___x_3285_ = lean_unsigned_to_nat(0u);
v___x_3286_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3283_, v_decls_3284_, v_exceptFVars_3282_, v___x_3285_, v___x_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3287_, lean_object* v_lctx_u2082_3288_, lean_object* v_exceptFVars_3289_){
_start:
{
uint8_t v_res_3290_; lean_object* v_r_3291_; 
v_res_3290_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3287_, v_lctx_u2082_3288_, v_exceptFVars_3289_);
lean_dec_ref(v_exceptFVars_3289_);
lean_dec_ref(v_lctx_u2082_3288_);
lean_dec_ref(v_lctx_u2081_3287_);
v_r_3291_ = lean_box(v_res_3290_);
return v_r_3291_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3293_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3294_ = lean_unsigned_to_nat(14u);
v___x_3295_ = lean_unsigned_to_nat(573u);
v___x_3296_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3297_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3298_ = l_mkPanicMessageWithDecl(v___x_3297_, v___x_3296_, v___x_3295_, v___x_3294_, v___x_3293_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3299_, lean_object* v_lctx_3300_, lean_object* v___x_3301_, uint8_t v_isLambda_3302_, uint8_t v_usedLetOnly_3303_, uint8_t v_generalizeNondepLet_3304_, lean_object* v_i_3305_, lean_object* v_x_3306_, lean_object* v_b_3307_){
_start:
{
lean_object* v_n_3309_; lean_object* v_ty_3310_; uint8_t v_bi_3311_; lean_object* v_x_3315_; lean_object* v___x_3316_; 
v_x_3315_ = lean_array_fget_borrowed(v_xs_3299_, v_i_3305_);
v___x_3316_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3300_, v_x_3315_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_dec_ref(v_b_3307_);
v___x_3317_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3318_ = l_panic___redArg(v___x_3301_, v___x_3317_);
return v___x_3318_;
}
else
{
lean_object* v_val_3319_; 
v_val_3319_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_val_3319_);
lean_dec_ref(v___x_3316_);
if (lean_obj_tag(v_val_3319_) == 0)
{
lean_object* v_userName_3320_; lean_object* v_type_3321_; uint8_t v_bi_3322_; 
v_userName_3320_ = lean_ctor_get(v_val_3319_, 2);
lean_inc(v_userName_3320_);
v_type_3321_ = lean_ctor_get(v_val_3319_, 3);
lean_inc_ref(v_type_3321_);
v_bi_3322_ = lean_ctor_get_uint8(v_val_3319_, sizeof(void*)*4);
lean_dec_ref(v_val_3319_);
v_n_3309_ = v_userName_3320_;
v_ty_3310_ = v_type_3321_;
v_bi_3311_ = v_bi_3322_;
goto v___jp_3308_;
}
else
{
lean_object* v_userName_3323_; lean_object* v_type_3324_; lean_object* v_value_3325_; uint8_t v_nondep_3326_; uint8_t v___y_3332_; 
v_userName_3323_ = lean_ctor_get(v_val_3319_, 2);
lean_inc(v_userName_3323_);
v_type_3324_ = lean_ctor_get(v_val_3319_, 3);
lean_inc_ref(v_type_3324_);
v_value_3325_ = lean_ctor_get(v_val_3319_, 4);
lean_inc_ref(v_value_3325_);
v_nondep_3326_ = lean_ctor_get_uint8(v_val_3319_, sizeof(void*)*5);
lean_dec_ref(v_val_3319_);
if (v_nondep_3326_ == 0)
{
v___y_3332_ = v_nondep_3326_;
goto v___jp_3331_;
}
else
{
if (v_generalizeNondepLet_3304_ == 0)
{
v___y_3332_ = v_generalizeNondepLet_3304_;
goto v___jp_3331_;
}
else
{
uint8_t v___x_3337_; 
lean_dec_ref(v_value_3325_);
v___x_3337_ = 0;
v_n_3309_ = v_userName_3323_;
v_ty_3310_ = v_type_3324_;
v_bi_3311_ = v___x_3337_;
goto v___jp_3308_;
}
}
v___jp_3327_:
{
lean_object* v_ty_3328_; lean_object* v_val_3329_; lean_object* v___x_3330_; 
v_ty_3328_ = lean_expr_abstract_range(v_type_3324_, v_i_3305_, v_xs_3299_);
lean_dec_ref(v_type_3324_);
v_val_3329_ = lean_expr_abstract_range(v_value_3325_, v_i_3305_, v_xs_3299_);
lean_dec_ref(v_value_3325_);
v___x_3330_ = l_Lean_Expr_letE___override(v_userName_3323_, v_ty_3328_, v_val_3329_, v_b_3307_, v_nondep_3326_);
return v___x_3330_;
}
v___jp_3331_:
{
if (v_usedLetOnly_3303_ == 0)
{
goto v___jp_3327_;
}
else
{
if (v___y_3332_ == 0)
{
lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3333_ = lean_unsigned_to_nat(0u);
v___x_3334_ = lean_expr_has_loose_bvar(v_b_3307_, v___x_3333_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
lean_dec_ref(v_value_3325_);
lean_dec_ref(v_type_3324_);
lean_dec(v_userName_3323_);
v___x_3335_ = lean_unsigned_to_nat(1u);
v___x_3336_ = lean_expr_lower_loose_bvars(v_b_3307_, v___x_3335_, v___x_3335_);
lean_dec_ref(v_b_3307_);
return v___x_3336_;
}
else
{
goto v___jp_3327_;
}
}
else
{
goto v___jp_3327_;
}
}
}
}
}
v___jp_3308_:
{
lean_object* v_ty_3312_; 
v_ty_3312_ = lean_expr_abstract_range(v_ty_3310_, v_i_3305_, v_xs_3299_);
lean_dec_ref(v_ty_3310_);
if (v_isLambda_3302_ == 0)
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_mkForall(v_n_3309_, v_bi_3311_, v_ty_3312_, v_b_3307_);
return v___x_3313_;
}
else
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Lean_mkLambda(v_n_3309_, v_bi_3311_, v_ty_3312_, v_b_3307_);
return v___x_3314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3338_, lean_object* v_lctx_3339_, lean_object* v___x_3340_, lean_object* v_isLambda_3341_, lean_object* v_usedLetOnly_3342_, lean_object* v_generalizeNondepLet_3343_, lean_object* v_i_3344_, lean_object* v_x_3345_, lean_object* v_b_3346_){
_start:
{
uint8_t v_isLambda_boxed_3347_; uint8_t v_usedLetOnly_boxed_3348_; uint8_t v_generalizeNondepLet_boxed_3349_; lean_object* v_res_3350_; 
v_isLambda_boxed_3347_ = lean_unbox(v_isLambda_3341_);
v_usedLetOnly_boxed_3348_ = lean_unbox(v_usedLetOnly_3342_);
v_generalizeNondepLet_boxed_3349_ = lean_unbox(v_generalizeNondepLet_3343_);
v_res_3350_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3338_, v_lctx_3339_, v___x_3340_, v_isLambda_boxed_3347_, v_usedLetOnly_boxed_3348_, v_generalizeNondepLet_boxed_3349_, v_i_3344_, v_x_3345_, v_b_3346_);
lean_dec(v_i_3344_);
lean_dec_ref(v___x_3340_);
lean_dec_ref(v_xs_3338_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3351_, lean_object* v_lctx_3352_, lean_object* v_xs_3353_, lean_object* v_b_3354_, uint8_t v_usedLetOnly_3355_, uint8_t v_generalizeNondepLet_3356_){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___f_3361_; lean_object* v_b_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3357_ = l_Lean_instInhabitedExpr;
v___x_3358_ = lean_box(v_isLambda_3351_);
v___x_3359_ = lean_box(v_usedLetOnly_3355_);
v___x_3360_ = lean_box(v_generalizeNondepLet_3356_);
lean_inc_ref(v_xs_3353_);
v___f_3361_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3361_, 0, v_xs_3353_);
lean_closure_set(v___f_3361_, 1, v_lctx_3352_);
lean_closure_set(v___f_3361_, 2, v___x_3357_);
lean_closure_set(v___f_3361_, 3, v___x_3358_);
lean_closure_set(v___f_3361_, 4, v___x_3359_);
lean_closure_set(v___f_3361_, 5, v___x_3360_);
v_b_3362_ = lean_expr_abstract(v_b_3354_, v_xs_3353_);
v___x_3363_ = lean_array_get_size(v_xs_3353_);
lean_dec_ref(v_xs_3353_);
v___x_3364_ = l_Nat_foldRev___redArg(v___x_3363_, v___f_3361_, v_b_3362_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3365_, lean_object* v_lctx_3366_, lean_object* v_xs_3367_, lean_object* v_b_3368_, lean_object* v_usedLetOnly_3369_, lean_object* v_generalizeNondepLet_3370_){
_start:
{
uint8_t v_isLambda_boxed_3371_; uint8_t v_usedLetOnly_boxed_3372_; uint8_t v_generalizeNondepLet_boxed_3373_; lean_object* v_res_3374_; 
v_isLambda_boxed_3371_ = lean_unbox(v_isLambda_3365_);
v_usedLetOnly_boxed_3372_ = lean_unbox(v_usedLetOnly_3369_);
v_generalizeNondepLet_boxed_3373_ = lean_unbox(v_generalizeNondepLet_3370_);
v_res_3374_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3371_, v_lctx_3366_, v_xs_3367_, v_b_3368_, v_usedLetOnly_boxed_3372_, v_generalizeNondepLet_boxed_3373_);
lean_dec_ref(v_b_3368_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3375_, lean_object* v_lctx_3376_, uint8_t v_usedLetOnly_3377_, uint8_t v_generalizeNondepLet_3378_, lean_object* v_x_3379_, lean_object* v_x_3380_){
_start:
{
lean_object* v_zero_3381_; uint8_t v_isZero_3382_; 
v_zero_3381_ = lean_unsigned_to_nat(0u);
v_isZero_3382_ = lean_nat_dec_eq(v_x_3379_, v_zero_3381_);
if (v_isZero_3382_ == 1)
{
lean_dec(v_x_3379_);
lean_dec_ref(v_lctx_3376_);
return v_x_3380_;
}
else
{
lean_object* v_one_3383_; lean_object* v_n_3384_; lean_object* v_n_3386_; lean_object* v_ty_3387_; uint8_t v_bi_3388_; lean_object* v_x_3392_; lean_object* v___x_3393_; 
v_one_3383_ = lean_unsigned_to_nat(1u);
v_n_3384_ = lean_nat_sub(v_x_3379_, v_one_3383_);
lean_dec(v_x_3379_);
v_x_3392_ = lean_array_fget_borrowed(v_xs_3375_, v_n_3384_);
lean_inc_ref(v_lctx_3376_);
v___x_3393_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3376_, v_x_3392_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_dec_ref(v_x_3380_);
v___x_3394_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3395_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3394_);
v_x_3379_ = v_n_3384_;
v_x_3380_ = v___x_3395_;
goto _start;
}
else
{
lean_object* v_val_3397_; 
v_val_3397_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_val_3397_);
lean_dec_ref(v___x_3393_);
if (lean_obj_tag(v_val_3397_) == 0)
{
lean_object* v_userName_3398_; lean_object* v_type_3399_; uint8_t v_bi_3400_; 
v_userName_3398_ = lean_ctor_get(v_val_3397_, 2);
lean_inc(v_userName_3398_);
v_type_3399_ = lean_ctor_get(v_val_3397_, 3);
lean_inc_ref(v_type_3399_);
v_bi_3400_ = lean_ctor_get_uint8(v_val_3397_, sizeof(void*)*4);
lean_dec_ref(v_val_3397_);
v_n_3386_ = v_userName_3398_;
v_ty_3387_ = v_type_3399_;
v_bi_3388_ = v_bi_3400_;
goto v___jp_3385_;
}
else
{
lean_object* v_userName_3401_; lean_object* v_type_3402_; lean_object* v_value_3403_; uint8_t v_nondep_3404_; uint8_t v___y_3411_; 
v_userName_3401_ = lean_ctor_get(v_val_3397_, 2);
lean_inc(v_userName_3401_);
v_type_3402_ = lean_ctor_get(v_val_3397_, 3);
lean_inc_ref(v_type_3402_);
v_value_3403_ = lean_ctor_get(v_val_3397_, 4);
lean_inc_ref(v_value_3403_);
v_nondep_3404_ = lean_ctor_get_uint8(v_val_3397_, sizeof(void*)*5);
lean_dec_ref(v_val_3397_);
if (v_nondep_3404_ == 0)
{
v___y_3411_ = v_nondep_3404_;
goto v___jp_3410_;
}
else
{
if (v_generalizeNondepLet_3378_ == 0)
{
v___y_3411_ = v_generalizeNondepLet_3378_;
goto v___jp_3410_;
}
else
{
uint8_t v___x_3415_; 
lean_dec_ref(v_value_3403_);
v___x_3415_ = 0;
v_n_3386_ = v_userName_3401_;
v_ty_3387_ = v_type_3402_;
v_bi_3388_ = v___x_3415_;
goto v___jp_3385_;
}
}
v___jp_3405_:
{
lean_object* v_ty_3406_; lean_object* v_val_3407_; lean_object* v___x_3408_; 
v_ty_3406_ = lean_expr_abstract_range(v_type_3402_, v_n_3384_, v_xs_3375_);
lean_dec_ref(v_type_3402_);
v_val_3407_ = lean_expr_abstract_range(v_value_3403_, v_n_3384_, v_xs_3375_);
lean_dec_ref(v_value_3403_);
v___x_3408_ = l_Lean_Expr_letE___override(v_userName_3401_, v_ty_3406_, v_val_3407_, v_x_3380_, v_nondep_3404_);
v_x_3379_ = v_n_3384_;
v_x_3380_ = v___x_3408_;
goto _start;
}
v___jp_3410_:
{
if (v_usedLetOnly_3377_ == 0)
{
goto v___jp_3405_;
}
else
{
if (v___y_3411_ == 0)
{
uint8_t v___x_3412_; 
v___x_3412_ = lean_expr_has_loose_bvar(v_x_3380_, v_zero_3381_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; 
lean_dec_ref(v_value_3403_);
lean_dec_ref(v_type_3402_);
lean_dec(v_userName_3401_);
v___x_3413_ = lean_expr_lower_loose_bvars(v_x_3380_, v_one_3383_, v_one_3383_);
lean_dec_ref(v_x_3380_);
v_x_3379_ = v_n_3384_;
v_x_3380_ = v___x_3413_;
goto _start;
}
else
{
goto v___jp_3405_;
}
}
else
{
goto v___jp_3405_;
}
}
}
}
}
v___jp_3385_:
{
lean_object* v_ty_3389_; lean_object* v___x_3390_; 
v_ty_3389_ = lean_expr_abstract_range(v_ty_3387_, v_n_3384_, v_xs_3375_);
lean_dec_ref(v_ty_3387_);
v___x_3390_ = l_Lean_mkLambda(v_n_3386_, v_bi_3388_, v_ty_3389_, v_x_3380_);
v_x_3379_ = v_n_3384_;
v_x_3380_ = v___x_3390_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3416_, lean_object* v_lctx_3417_, lean_object* v_usedLetOnly_3418_, lean_object* v_generalizeNondepLet_3419_, lean_object* v_x_3420_, lean_object* v_x_3421_){
_start:
{
uint8_t v_usedLetOnly_boxed_3422_; uint8_t v_generalizeNondepLet_boxed_3423_; lean_object* v_res_3424_; 
v_usedLetOnly_boxed_3422_ = lean_unbox(v_usedLetOnly_3418_);
v_generalizeNondepLet_boxed_3423_ = lean_unbox(v_generalizeNondepLet_3419_);
v_res_3424_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3416_, v_lctx_3417_, v_usedLetOnly_boxed_3422_, v_generalizeNondepLet_boxed_3423_, v_x_3420_, v_x_3421_);
lean_dec_ref(v_xs_3416_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3425_, lean_object* v_lctx_3426_, uint8_t v_usedLetOnly_3427_, uint8_t v_generalizeNondepLet_3428_, lean_object* v_x_3429_, lean_object* v_x_3430_){
_start:
{
lean_object* v_zero_3431_; uint8_t v_isZero_3432_; 
v_zero_3431_ = lean_unsigned_to_nat(0u);
v_isZero_3432_ = lean_nat_dec_eq(v_x_3429_, v_zero_3431_);
if (v_isZero_3432_ == 1)
{
lean_dec_ref(v_lctx_3426_);
return v_x_3430_;
}
else
{
lean_object* v_one_3433_; lean_object* v_n_3434_; lean_object* v_n_3436_; lean_object* v_ty_3437_; uint8_t v_bi_3438_; lean_object* v_x_3442_; lean_object* v___x_3443_; 
v_one_3433_ = lean_unsigned_to_nat(1u);
v_n_3434_ = lean_nat_sub(v_x_3429_, v_one_3433_);
v_x_3442_ = lean_array_fget_borrowed(v_xs_3425_, v_n_3434_);
lean_inc_ref(v_lctx_3426_);
v___x_3443_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3426_, v_x_3442_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
lean_dec_ref(v_x_3430_);
v___x_3444_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3445_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3444_);
v___x_3446_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3425_, v_lctx_3426_, v_usedLetOnly_3427_, v_generalizeNondepLet_3428_, v_n_3434_, v___x_3445_);
return v___x_3446_;
}
else
{
lean_object* v_val_3447_; 
v_val_3447_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_val_3447_);
lean_dec_ref(v___x_3443_);
if (lean_obj_tag(v_val_3447_) == 0)
{
lean_object* v_userName_3448_; lean_object* v_type_3449_; uint8_t v_bi_3450_; 
v_userName_3448_ = lean_ctor_get(v_val_3447_, 2);
lean_inc(v_userName_3448_);
v_type_3449_ = lean_ctor_get(v_val_3447_, 3);
lean_inc_ref(v_type_3449_);
v_bi_3450_ = lean_ctor_get_uint8(v_val_3447_, sizeof(void*)*4);
lean_dec_ref(v_val_3447_);
v_n_3436_ = v_userName_3448_;
v_ty_3437_ = v_type_3449_;
v_bi_3438_ = v_bi_3450_;
goto v___jp_3435_;
}
else
{
lean_object* v_userName_3451_; lean_object* v_type_3452_; lean_object* v_value_3453_; uint8_t v_nondep_3454_; uint8_t v___y_3461_; 
v_userName_3451_ = lean_ctor_get(v_val_3447_, 2);
lean_inc(v_userName_3451_);
v_type_3452_ = lean_ctor_get(v_val_3447_, 3);
lean_inc_ref(v_type_3452_);
v_value_3453_ = lean_ctor_get(v_val_3447_, 4);
lean_inc_ref(v_value_3453_);
v_nondep_3454_ = lean_ctor_get_uint8(v_val_3447_, sizeof(void*)*5);
lean_dec_ref(v_val_3447_);
if (v_nondep_3454_ == 0)
{
v___y_3461_ = v_nondep_3454_;
goto v___jp_3460_;
}
else
{
if (v_generalizeNondepLet_3428_ == 0)
{
v___y_3461_ = v_generalizeNondepLet_3428_;
goto v___jp_3460_;
}
else
{
uint8_t v___x_3465_; 
lean_dec_ref(v_value_3453_);
v___x_3465_ = 0;
v_n_3436_ = v_userName_3451_;
v_ty_3437_ = v_type_3452_;
v_bi_3438_ = v___x_3465_;
goto v___jp_3435_;
}
}
v___jp_3455_:
{
lean_object* v_ty_3456_; lean_object* v_val_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v_ty_3456_ = lean_expr_abstract_range(v_type_3452_, v_n_3434_, v_xs_3425_);
lean_dec_ref(v_type_3452_);
v_val_3457_ = lean_expr_abstract_range(v_value_3453_, v_n_3434_, v_xs_3425_);
lean_dec_ref(v_value_3453_);
v___x_3458_ = l_Lean_Expr_letE___override(v_userName_3451_, v_ty_3456_, v_val_3457_, v_x_3430_, v_nondep_3454_);
v___x_3459_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3425_, v_lctx_3426_, v_usedLetOnly_3427_, v_generalizeNondepLet_3428_, v_n_3434_, v___x_3458_);
return v___x_3459_;
}
v___jp_3460_:
{
if (v_usedLetOnly_3427_ == 0)
{
goto v___jp_3455_;
}
else
{
if (v___y_3461_ == 0)
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_expr_has_loose_bvar(v_x_3430_, v_zero_3431_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_dec_ref(v_value_3453_);
lean_dec_ref(v_type_3452_);
lean_dec(v_userName_3451_);
v___x_3463_ = lean_expr_lower_loose_bvars(v_x_3430_, v_one_3433_, v_one_3433_);
lean_dec_ref(v_x_3430_);
v___x_3464_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3425_, v_lctx_3426_, v_usedLetOnly_3427_, v_generalizeNondepLet_3428_, v_n_3434_, v___x_3463_);
return v___x_3464_;
}
else
{
goto v___jp_3455_;
}
}
else
{
goto v___jp_3455_;
}
}
}
}
}
v___jp_3435_:
{
lean_object* v_ty_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v_ty_3439_ = lean_expr_abstract_range(v_ty_3437_, v_n_3434_, v_xs_3425_);
lean_dec_ref(v_ty_3437_);
v___x_3440_ = l_Lean_mkLambda(v_n_3436_, v_bi_3438_, v_ty_3439_, v_x_3430_);
v___x_3441_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3425_, v_lctx_3426_, v_usedLetOnly_3427_, v_generalizeNondepLet_3428_, v_n_3434_, v___x_3440_);
return v___x_3441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3466_, lean_object* v_lctx_3467_, lean_object* v_usedLetOnly_3468_, lean_object* v_generalizeNondepLet_3469_, lean_object* v_x_3470_, lean_object* v_x_3471_){
_start:
{
uint8_t v_usedLetOnly_boxed_3472_; uint8_t v_generalizeNondepLet_boxed_3473_; lean_object* v_res_3474_; 
v_usedLetOnly_boxed_3472_ = lean_unbox(v_usedLetOnly_3468_);
v_generalizeNondepLet_boxed_3473_ = lean_unbox(v_generalizeNondepLet_3469_);
v_res_3474_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3466_, v_lctx_3467_, v_usedLetOnly_boxed_3472_, v_generalizeNondepLet_boxed_3473_, v_x_3470_, v_x_3471_);
lean_dec(v_x_3470_);
lean_dec_ref(v_xs_3466_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3475_, lean_object* v_xs_3476_, lean_object* v_b_3477_, uint8_t v_usedLetOnly_3478_, uint8_t v_generalizeNondepLet_3479_){
_start:
{
lean_object* v_b_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v_b_3480_ = lean_expr_abstract(v_b_3477_, v_xs_3476_);
v___x_3481_ = lean_array_get_size(v_xs_3476_);
v___x_3482_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3476_, v_lctx_3475_, v_usedLetOnly_3478_, v_generalizeNondepLet_3479_, v___x_3481_, v_b_3480_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3483_, lean_object* v_xs_3484_, lean_object* v_b_3485_, lean_object* v_usedLetOnly_3486_, lean_object* v_generalizeNondepLet_3487_){
_start:
{
uint8_t v_usedLetOnly_boxed_3488_; uint8_t v_generalizeNondepLet_boxed_3489_; lean_object* v_res_3490_; 
v_usedLetOnly_boxed_3488_ = lean_unbox(v_usedLetOnly_3486_);
v_generalizeNondepLet_boxed_3489_ = lean_unbox(v_generalizeNondepLet_3487_);
v_res_3490_ = l_Lean_LocalContext_mkLambda(v_lctx_3483_, v_xs_3484_, v_b_3485_, v_usedLetOnly_boxed_3488_, v_generalizeNondepLet_boxed_3489_);
lean_dec_ref(v_b_3485_);
lean_dec_ref(v_xs_3484_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3491_, lean_object* v_lctx_3492_, uint8_t v_usedLetOnly_3493_, uint8_t v_generalizeNondepLet_3494_, lean_object* v_x_3495_, lean_object* v_x_3496_){
_start:
{
lean_object* v_zero_3497_; uint8_t v_isZero_3498_; 
v_zero_3497_ = lean_unsigned_to_nat(0u);
v_isZero_3498_ = lean_nat_dec_eq(v_x_3495_, v_zero_3497_);
if (v_isZero_3498_ == 1)
{
lean_dec(v_x_3495_);
lean_dec_ref(v_lctx_3492_);
return v_x_3496_;
}
else
{
lean_object* v_one_3499_; lean_object* v_n_3500_; lean_object* v_n_3502_; lean_object* v_ty_3503_; uint8_t v_bi_3504_; lean_object* v_x_3508_; lean_object* v___x_3509_; 
v_one_3499_ = lean_unsigned_to_nat(1u);
v_n_3500_ = lean_nat_sub(v_x_3495_, v_one_3499_);
lean_dec(v_x_3495_);
v_x_3508_ = lean_array_fget_borrowed(v_xs_3491_, v_n_3500_);
lean_inc_ref(v_lctx_3492_);
v___x_3509_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3492_, v_x_3508_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
lean_dec_ref(v_x_3496_);
v___x_3510_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3511_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3510_);
v_x_3495_ = v_n_3500_;
v_x_3496_ = v___x_3511_;
goto _start;
}
else
{
lean_object* v_val_3513_; 
v_val_3513_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_val_3513_);
lean_dec_ref(v___x_3509_);
if (lean_obj_tag(v_val_3513_) == 0)
{
lean_object* v_userName_3514_; lean_object* v_type_3515_; uint8_t v_bi_3516_; 
v_userName_3514_ = lean_ctor_get(v_val_3513_, 2);
lean_inc(v_userName_3514_);
v_type_3515_ = lean_ctor_get(v_val_3513_, 3);
lean_inc_ref(v_type_3515_);
v_bi_3516_ = lean_ctor_get_uint8(v_val_3513_, sizeof(void*)*4);
lean_dec_ref(v_val_3513_);
v_n_3502_ = v_userName_3514_;
v_ty_3503_ = v_type_3515_;
v_bi_3504_ = v_bi_3516_;
goto v___jp_3501_;
}
else
{
lean_object* v_userName_3517_; lean_object* v_type_3518_; lean_object* v_value_3519_; uint8_t v_nondep_3520_; uint8_t v___y_3527_; 
v_userName_3517_ = lean_ctor_get(v_val_3513_, 2);
lean_inc(v_userName_3517_);
v_type_3518_ = lean_ctor_get(v_val_3513_, 3);
lean_inc_ref(v_type_3518_);
v_value_3519_ = lean_ctor_get(v_val_3513_, 4);
lean_inc_ref(v_value_3519_);
v_nondep_3520_ = lean_ctor_get_uint8(v_val_3513_, sizeof(void*)*5);
lean_dec_ref(v_val_3513_);
if (v_nondep_3520_ == 0)
{
v___y_3527_ = v_nondep_3520_;
goto v___jp_3526_;
}
else
{
if (v_generalizeNondepLet_3494_ == 0)
{
v___y_3527_ = v_generalizeNondepLet_3494_;
goto v___jp_3526_;
}
else
{
uint8_t v___x_3531_; 
lean_dec_ref(v_value_3519_);
v___x_3531_ = 0;
v_n_3502_ = v_userName_3517_;
v_ty_3503_ = v_type_3518_;
v_bi_3504_ = v___x_3531_;
goto v___jp_3501_;
}
}
v___jp_3521_:
{
lean_object* v_ty_3522_; lean_object* v_val_3523_; lean_object* v___x_3524_; 
v_ty_3522_ = lean_expr_abstract_range(v_type_3518_, v_n_3500_, v_xs_3491_);
lean_dec_ref(v_type_3518_);
v_val_3523_ = lean_expr_abstract_range(v_value_3519_, v_n_3500_, v_xs_3491_);
lean_dec_ref(v_value_3519_);
v___x_3524_ = l_Lean_Expr_letE___override(v_userName_3517_, v_ty_3522_, v_val_3523_, v_x_3496_, v_nondep_3520_);
v_x_3495_ = v_n_3500_;
v_x_3496_ = v___x_3524_;
goto _start;
}
v___jp_3526_:
{
if (v_usedLetOnly_3493_ == 0)
{
goto v___jp_3521_;
}
else
{
if (v___y_3527_ == 0)
{
uint8_t v___x_3528_; 
v___x_3528_ = lean_expr_has_loose_bvar(v_x_3496_, v_zero_3497_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; 
lean_dec_ref(v_value_3519_);
lean_dec_ref(v_type_3518_);
lean_dec(v_userName_3517_);
v___x_3529_ = lean_expr_lower_loose_bvars(v_x_3496_, v_one_3499_, v_one_3499_);
lean_dec_ref(v_x_3496_);
v_x_3495_ = v_n_3500_;
v_x_3496_ = v___x_3529_;
goto _start;
}
else
{
goto v___jp_3521_;
}
}
else
{
goto v___jp_3521_;
}
}
}
}
}
v___jp_3501_:
{
lean_object* v_ty_3505_; lean_object* v___x_3506_; 
v_ty_3505_ = lean_expr_abstract_range(v_ty_3503_, v_n_3500_, v_xs_3491_);
lean_dec_ref(v_ty_3503_);
v___x_3506_ = l_Lean_mkForall(v_n_3502_, v_bi_3504_, v_ty_3505_, v_x_3496_);
v_x_3495_ = v_n_3500_;
v_x_3496_ = v___x_3506_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3532_, lean_object* v_lctx_3533_, lean_object* v_usedLetOnly_3534_, lean_object* v_generalizeNondepLet_3535_, lean_object* v_x_3536_, lean_object* v_x_3537_){
_start:
{
uint8_t v_usedLetOnly_boxed_3538_; uint8_t v_generalizeNondepLet_boxed_3539_; lean_object* v_res_3540_; 
v_usedLetOnly_boxed_3538_ = lean_unbox(v_usedLetOnly_3534_);
v_generalizeNondepLet_boxed_3539_ = lean_unbox(v_generalizeNondepLet_3535_);
v_res_3540_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3532_, v_lctx_3533_, v_usedLetOnly_boxed_3538_, v_generalizeNondepLet_boxed_3539_, v_x_3536_, v_x_3537_);
lean_dec_ref(v_xs_3532_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3541_, lean_object* v_lctx_3542_, uint8_t v_usedLetOnly_3543_, uint8_t v_generalizeNondepLet_3544_, lean_object* v_x_3545_, lean_object* v_x_3546_){
_start:
{
lean_object* v_zero_3547_; uint8_t v_isZero_3548_; 
v_zero_3547_ = lean_unsigned_to_nat(0u);
v_isZero_3548_ = lean_nat_dec_eq(v_x_3545_, v_zero_3547_);
if (v_isZero_3548_ == 1)
{
lean_dec_ref(v_lctx_3542_);
return v_x_3546_;
}
else
{
lean_object* v_one_3549_; lean_object* v_n_3550_; lean_object* v_n_3552_; lean_object* v_ty_3553_; uint8_t v_bi_3554_; lean_object* v_x_3558_; lean_object* v___x_3559_; 
v_one_3549_ = lean_unsigned_to_nat(1u);
v_n_3550_ = lean_nat_sub(v_x_3545_, v_one_3549_);
v_x_3558_ = lean_array_fget_borrowed(v_xs_3541_, v_n_3550_);
lean_inc_ref(v_lctx_3542_);
v___x_3559_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3542_, v_x_3558_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
lean_dec_ref(v_x_3546_);
v___x_3560_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3561_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3560_);
v___x_3562_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3541_, v_lctx_3542_, v_usedLetOnly_3543_, v_generalizeNondepLet_3544_, v_n_3550_, v___x_3561_);
return v___x_3562_;
}
else
{
lean_object* v_val_3563_; 
v_val_3563_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_val_3563_);
lean_dec_ref(v___x_3559_);
if (lean_obj_tag(v_val_3563_) == 0)
{
lean_object* v_userName_3564_; lean_object* v_type_3565_; uint8_t v_bi_3566_; 
v_userName_3564_ = lean_ctor_get(v_val_3563_, 2);
lean_inc(v_userName_3564_);
v_type_3565_ = lean_ctor_get(v_val_3563_, 3);
lean_inc_ref(v_type_3565_);
v_bi_3566_ = lean_ctor_get_uint8(v_val_3563_, sizeof(void*)*4);
lean_dec_ref(v_val_3563_);
v_n_3552_ = v_userName_3564_;
v_ty_3553_ = v_type_3565_;
v_bi_3554_ = v_bi_3566_;
goto v___jp_3551_;
}
else
{
lean_object* v_userName_3567_; lean_object* v_type_3568_; lean_object* v_value_3569_; uint8_t v_nondep_3570_; uint8_t v___y_3577_; 
v_userName_3567_ = lean_ctor_get(v_val_3563_, 2);
lean_inc(v_userName_3567_);
v_type_3568_ = lean_ctor_get(v_val_3563_, 3);
lean_inc_ref(v_type_3568_);
v_value_3569_ = lean_ctor_get(v_val_3563_, 4);
lean_inc_ref(v_value_3569_);
v_nondep_3570_ = lean_ctor_get_uint8(v_val_3563_, sizeof(void*)*5);
lean_dec_ref(v_val_3563_);
if (v_nondep_3570_ == 0)
{
v___y_3577_ = v_nondep_3570_;
goto v___jp_3576_;
}
else
{
if (v_generalizeNondepLet_3544_ == 0)
{
v___y_3577_ = v_generalizeNondepLet_3544_;
goto v___jp_3576_;
}
else
{
uint8_t v___x_3581_; 
lean_dec_ref(v_value_3569_);
v___x_3581_ = 0;
v_n_3552_ = v_userName_3567_;
v_ty_3553_ = v_type_3568_;
v_bi_3554_ = v___x_3581_;
goto v___jp_3551_;
}
}
v___jp_3571_:
{
lean_object* v_ty_3572_; lean_object* v_val_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v_ty_3572_ = lean_expr_abstract_range(v_type_3568_, v_n_3550_, v_xs_3541_);
lean_dec_ref(v_type_3568_);
v_val_3573_ = lean_expr_abstract_range(v_value_3569_, v_n_3550_, v_xs_3541_);
lean_dec_ref(v_value_3569_);
v___x_3574_ = l_Lean_Expr_letE___override(v_userName_3567_, v_ty_3572_, v_val_3573_, v_x_3546_, v_nondep_3570_);
v___x_3575_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3541_, v_lctx_3542_, v_usedLetOnly_3543_, v_generalizeNondepLet_3544_, v_n_3550_, v___x_3574_);
return v___x_3575_;
}
v___jp_3576_:
{
if (v_usedLetOnly_3543_ == 0)
{
goto v___jp_3571_;
}
else
{
if (v___y_3577_ == 0)
{
uint8_t v___x_3578_; 
v___x_3578_ = lean_expr_has_loose_bvar(v_x_3546_, v_zero_3547_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_dec_ref(v_value_3569_);
lean_dec_ref(v_type_3568_);
lean_dec(v_userName_3567_);
v___x_3579_ = lean_expr_lower_loose_bvars(v_x_3546_, v_one_3549_, v_one_3549_);
lean_dec_ref(v_x_3546_);
v___x_3580_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3541_, v_lctx_3542_, v_usedLetOnly_3543_, v_generalizeNondepLet_3544_, v_n_3550_, v___x_3579_);
return v___x_3580_;
}
else
{
goto v___jp_3571_;
}
}
else
{
goto v___jp_3571_;
}
}
}
}
}
v___jp_3551_:
{
lean_object* v_ty_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v_ty_3555_ = lean_expr_abstract_range(v_ty_3553_, v_n_3550_, v_xs_3541_);
lean_dec_ref(v_ty_3553_);
v___x_3556_ = l_Lean_mkForall(v_n_3552_, v_bi_3554_, v_ty_3555_, v_x_3546_);
v___x_3557_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3541_, v_lctx_3542_, v_usedLetOnly_3543_, v_generalizeNondepLet_3544_, v_n_3550_, v___x_3556_);
return v___x_3557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3582_, lean_object* v_lctx_3583_, lean_object* v_usedLetOnly_3584_, lean_object* v_generalizeNondepLet_3585_, lean_object* v_x_3586_, lean_object* v_x_3587_){
_start:
{
uint8_t v_usedLetOnly_boxed_3588_; uint8_t v_generalizeNondepLet_boxed_3589_; lean_object* v_res_3590_; 
v_usedLetOnly_boxed_3588_ = lean_unbox(v_usedLetOnly_3584_);
v_generalizeNondepLet_boxed_3589_ = lean_unbox(v_generalizeNondepLet_3585_);
v_res_3590_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3582_, v_lctx_3583_, v_usedLetOnly_boxed_3588_, v_generalizeNondepLet_boxed_3589_, v_x_3586_, v_x_3587_);
lean_dec(v_x_3586_);
lean_dec_ref(v_xs_3582_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3591_, lean_object* v_xs_3592_, lean_object* v_b_3593_, uint8_t v_usedLetOnly_3594_, uint8_t v_generalizeNondepLet_3595_){
_start:
{
lean_object* v_b_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v_b_3596_ = lean_expr_abstract(v_b_3593_, v_xs_3592_);
v___x_3597_ = lean_array_get_size(v_xs_3592_);
v___x_3598_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3592_, v_lctx_3591_, v_usedLetOnly_3594_, v_generalizeNondepLet_3595_, v___x_3597_, v_b_3596_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3599_, lean_object* v_xs_3600_, lean_object* v_b_3601_, lean_object* v_usedLetOnly_3602_, lean_object* v_generalizeNondepLet_3603_){
_start:
{
uint8_t v_usedLetOnly_boxed_3604_; uint8_t v_generalizeNondepLet_boxed_3605_; lean_object* v_res_3606_; 
v_usedLetOnly_boxed_3604_ = lean_unbox(v_usedLetOnly_3602_);
v_generalizeNondepLet_boxed_3605_ = lean_unbox(v_generalizeNondepLet_3603_);
v_res_3606_ = l_Lean_LocalContext_mkForall(v_lctx_3599_, v_xs_3600_, v_b_3601_, v_usedLetOnly_boxed_3604_, v_generalizeNondepLet_boxed_3605_);
lean_dec_ref(v_b_3601_);
lean_dec_ref(v_xs_3600_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3607_, lean_object* v_p_3608_, lean_object* v_d_3609_){
_start:
{
if (lean_obj_tag(v_d_3609_) == 0)
{
uint8_t v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
lean_dec(v_p_3608_);
v___x_3610_ = 0;
v___x_3611_ = lean_box(v___x_3610_);
v___x_3612_ = lean_apply_2(v_toPure_3607_, lean_box(0), v___x_3611_);
return v___x_3612_;
}
else
{
lean_object* v_val_3613_; lean_object* v___x_3614_; 
lean_dec(v_toPure_3607_);
v_val_3613_ = lean_ctor_get(v_d_3609_, 0);
lean_inc(v_val_3613_);
lean_dec_ref(v_d_3609_);
v___x_3614_ = lean_apply_1(v_p_3608_, v_val_3613_);
return v___x_3614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3615_, lean_object* v_lctx_3616_, lean_object* v_p_3617_){
_start:
{
lean_object* v_toApplicative_3618_; lean_object* v_decls_3619_; lean_object* v_toPure_3620_; lean_object* v___f_3621_; lean_object* v___x_3622_; 
v_toApplicative_3618_ = lean_ctor_get(v_inst_3615_, 0);
v_decls_3619_ = lean_ctor_get(v_lctx_3616_, 1);
lean_inc_ref(v_decls_3619_);
lean_dec_ref(v_lctx_3616_);
v_toPure_3620_ = lean_ctor_get(v_toApplicative_3618_, 1);
lean_inc(v_toPure_3620_);
v___f_3621_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3621_, 0, v_toPure_3620_);
lean_closure_set(v___f_3621_, 1, v_p_3617_);
v___x_3622_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3615_, v_decls_3619_, v___f_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3623_, lean_object* v_inst_3624_, lean_object* v_lctx_3625_, lean_object* v_p_3626_){
_start:
{
lean_object* v_toApplicative_3627_; lean_object* v_decls_3628_; lean_object* v_toPure_3629_; lean_object* v___f_3630_; lean_object* v___x_3631_; 
v_toApplicative_3627_ = lean_ctor_get(v_inst_3624_, 0);
v_decls_3628_ = lean_ctor_get(v_lctx_3625_, 1);
lean_inc_ref(v_decls_3628_);
lean_dec_ref(v_lctx_3625_);
v_toPure_3629_ = lean_ctor_get(v_toApplicative_3627_, 1);
lean_inc(v_toPure_3629_);
v___f_3630_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3630_, 0, v_toPure_3629_);
lean_closure_set(v___f_3630_, 1, v_p_3626_);
v___x_3631_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3624_, v_decls_3628_, v___f_3630_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3632_, uint8_t v_b_3633_){
_start:
{
if (v_b_3633_ == 0)
{
uint8_t v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3634_ = 1;
v___x_3635_ = lean_box(v___x_3634_);
v___x_3636_ = lean_apply_2(v_toPure_3632_, lean_box(0), v___x_3635_);
return v___x_3636_;
}
else
{
uint8_t v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3637_ = 0;
v___x_3638_ = lean_box(v___x_3637_);
v___x_3639_ = lean_apply_2(v_toPure_3632_, lean_box(0), v___x_3638_);
return v___x_3639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3640_, lean_object* v_b_3641_){
_start:
{
uint8_t v_b_boxed_3642_; lean_object* v_res_3643_; 
v_b_boxed_3642_ = lean_unbox(v_b_3641_);
v_res_3643_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3640_, v_b_boxed_3642_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3644_, lean_object* v_toBind_3645_, lean_object* v___f_3646_, lean_object* v_p_3647_, lean_object* v_v_3648_){
_start:
{
if (lean_obj_tag(v_v_3648_) == 0)
{
uint8_t v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
lean_dec(v_p_3647_);
v___x_3649_ = 1;
v___x_3650_ = lean_box(v___x_3649_);
v___x_3651_ = lean_apply_2(v_toPure_3644_, lean_box(0), v___x_3650_);
v___x_3652_ = lean_apply_4(v_toBind_3645_, lean_box(0), lean_box(0), v___x_3651_, v___f_3646_);
return v___x_3652_;
}
else
{
lean_object* v_val_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_dec(v_toPure_3644_);
v_val_3653_ = lean_ctor_get(v_v_3648_, 0);
lean_inc(v_val_3653_);
lean_dec_ref(v_v_3648_);
v___x_3654_ = lean_apply_1(v_p_3647_, v_val_3653_);
v___x_3655_ = lean_apply_4(v_toBind_3645_, lean_box(0), lean_box(0), v___x_3654_, v___f_3646_);
return v___x_3655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3656_, lean_object* v_lctx_3657_, lean_object* v_p_3658_){
_start:
{
lean_object* v_toApplicative_3659_; lean_object* v_decls_3660_; lean_object* v_toBind_3661_; lean_object* v_toPure_3662_; lean_object* v___f_3663_; lean_object* v___f_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v_toApplicative_3659_ = lean_ctor_get(v_inst_3656_, 0);
v_decls_3660_ = lean_ctor_get(v_lctx_3657_, 1);
lean_inc_ref(v_decls_3660_);
lean_dec_ref(v_lctx_3657_);
v_toBind_3661_ = lean_ctor_get(v_inst_3656_, 1);
lean_inc_n(v_toBind_3661_, 2);
v_toPure_3662_ = lean_ctor_get(v_toApplicative_3659_, 1);
lean_inc_n(v_toPure_3662_, 2);
v___f_3663_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3663_, 0, v_toPure_3662_);
lean_inc_ref(v___f_3663_);
v___f_3664_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3664_, 0, v_toPure_3662_);
lean_closure_set(v___f_3664_, 1, v_toBind_3661_);
lean_closure_set(v___f_3664_, 2, v___f_3663_);
lean_closure_set(v___f_3664_, 3, v_p_3658_);
v___x_3665_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3656_, v_decls_3660_, v___f_3664_);
v___x_3666_ = lean_apply_4(v_toBind_3661_, lean_box(0), lean_box(0), v___x_3665_, v___f_3663_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3667_, lean_object* v_inst_3668_, lean_object* v_lctx_3669_, lean_object* v_p_3670_){
_start:
{
lean_object* v_toApplicative_3671_; lean_object* v_decls_3672_; lean_object* v_toBind_3673_; lean_object* v_toPure_3674_; lean_object* v___f_3675_; lean_object* v___f_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v_toApplicative_3671_ = lean_ctor_get(v_inst_3668_, 0);
v_decls_3672_ = lean_ctor_get(v_lctx_3669_, 1);
lean_inc_ref(v_decls_3672_);
lean_dec_ref(v_lctx_3669_);
v_toBind_3673_ = lean_ctor_get(v_inst_3668_, 1);
lean_inc_n(v_toBind_3673_, 2);
v_toPure_3674_ = lean_ctor_get(v_toApplicative_3671_, 1);
lean_inc_n(v_toPure_3674_, 2);
v___f_3675_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3675_, 0, v_toPure_3674_);
lean_inc_ref(v___f_3675_);
v___f_3676_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3676_, 0, v_toPure_3674_);
lean_closure_set(v___f_3676_, 1, v_toBind_3673_);
lean_closure_set(v___f_3676_, 2, v___f_3675_);
lean_closure_set(v___f_3676_, 3, v_p_3670_);
v___x_3677_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3668_, v_decls_3672_, v___f_3676_);
v___x_3678_ = lean_apply_4(v_toBind_3673_, lean_box(0), lean_box(0), v___x_3677_, v___f_3675_);
return v___x_3678_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3679_, lean_object* v_d_3680_){
_start:
{
if (lean_obj_tag(v_d_3680_) == 0)
{
uint8_t v___x_3681_; 
lean_dec_ref(v_p_3679_);
v___x_3681_ = 0;
return v___x_3681_;
}
else
{
lean_object* v_val_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v_val_3682_ = lean_ctor_get(v_d_3680_, 0);
lean_inc(v_val_3682_);
lean_dec_ref(v_d_3680_);
v___x_3683_ = lean_apply_1(v_p_3679_, v_val_3682_);
v___x_3684_ = lean_unbox(v___x_3683_);
return v___x_3684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3685_, lean_object* v_d_3686_){
_start:
{
uint8_t v_res_3687_; lean_object* v_r_3688_; 
v_res_3687_ = l_Lean_LocalContext_any___lam__0(v_p_3685_, v_d_3686_);
v_r_3688_ = lean_box(v_res_3687_);
return v_r_3688_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3689_, lean_object* v_p_3690_){
_start:
{
lean_object* v___x_3691_; lean_object* v_decls_3692_; lean_object* v___f_3693_; lean_object* v___x_3694_; uint8_t v___x_3695_; 
v___x_3691_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3692_ = lean_ctor_get(v_lctx_3689_, 1);
lean_inc_ref(v_decls_3692_);
lean_dec_ref(v_lctx_3689_);
v___f_3693_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3693_, 0, v_p_3690_);
v___x_3694_ = l_Lean_PersistentArray_anyM___redArg(v___x_3691_, v_decls_3692_, v___f_3693_);
v___x_3695_ = lean_unbox(v___x_3694_);
lean_dec(v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3696_, lean_object* v_p_3697_){
_start:
{
uint8_t v_res_3698_; lean_object* v_r_3699_; 
v_res_3698_ = l_Lean_LocalContext_any(v_lctx_3696_, v_p_3697_);
v_r_3699_ = lean_box(v_res_3698_);
return v_r_3699_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3700_, lean_object* v_v_3701_){
_start:
{
if (lean_obj_tag(v_v_3701_) == 0)
{
uint8_t v___x_3702_; 
lean_dec_ref(v_p_3700_);
v___x_3702_ = 0;
return v___x_3702_;
}
else
{
lean_object* v_val_3703_; lean_object* v___x_3704_; uint8_t v___x_3705_; 
v_val_3703_ = lean_ctor_get(v_v_3701_, 0);
lean_inc(v_val_3703_);
lean_dec_ref(v_v_3701_);
v___x_3704_ = lean_apply_1(v_p_3700_, v_val_3703_);
v___x_3705_ = lean_unbox(v___x_3704_);
if (v___x_3705_ == 0)
{
uint8_t v___x_3706_; 
v___x_3706_ = 1;
return v___x_3706_;
}
else
{
uint8_t v___x_3707_; 
v___x_3707_ = 0;
return v___x_3707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3708_, lean_object* v_v_3709_){
_start:
{
uint8_t v_res_3710_; lean_object* v_r_3711_; 
v_res_3710_ = l_Lean_LocalContext_all___lam__0(v_p_3708_, v_v_3709_);
v_r_3711_ = lean_box(v_res_3710_);
return v_r_3711_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3712_, lean_object* v_p_3713_){
_start:
{
lean_object* v___x_3714_; lean_object* v_decls_3715_; lean_object* v___f_3716_; lean_object* v___x_3717_; uint8_t v___x_3718_; 
v___x_3714_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3715_ = lean_ctor_get(v_lctx_3712_, 1);
lean_inc_ref(v_decls_3715_);
lean_dec_ref(v_lctx_3712_);
v___f_3716_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3716_, 0, v_p_3713_);
v___x_3717_ = l_Lean_PersistentArray_anyM___redArg(v___x_3714_, v_decls_3715_, v___f_3716_);
v___x_3718_ = lean_unbox(v___x_3717_);
lean_dec(v___x_3717_);
if (v___x_3718_ == 0)
{
uint8_t v___x_3719_; 
v___x_3719_ = 1;
return v___x_3719_;
}
else
{
uint8_t v___x_3720_; 
v___x_3720_ = 0;
return v___x_3720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3721_, lean_object* v_p_3722_){
_start:
{
uint8_t v_res_3723_; lean_object* v_r_3724_; 
v_res_3723_ = l_Lean_LocalContext_all(v_lctx_3721_, v_p_3722_);
v_r_3724_ = lean_box(v_res_3723_);
return v_r_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3725_, lean_object* v_a_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v_zero_3729_; uint8_t v_isZero_3730_; 
v_zero_3729_ = lean_unsigned_to_nat(0u);
v_isZero_3730_ = lean_nat_dec_eq(v_i_3725_, v_zero_3729_);
if (v_isZero_3730_ == 1)
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
lean_dec(v_i_3725_);
v___x_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3731_, 0, v_a_3726_);
lean_ctor_set(v___x_3731_, 1, v___y_3727_);
v___x_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
lean_ctor_set(v___x_3732_, 1, v___y_3728_);
return v___x_3732_;
}
else
{
lean_object* v_decls_3733_; lean_object* v_size_3734_; lean_object* v_one_3735_; lean_object* v_n_3736_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3753_; lean_object* v___y_3754_; uint8_t v___y_3755_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3765_; lean_object* v___x_3769_; uint8_t v___x_3770_; 
v_decls_3733_ = lean_ctor_get(v_a_3726_, 1);
v_size_3734_ = lean_ctor_get(v_decls_3733_, 2);
v_one_3735_ = lean_unsigned_to_nat(1u);
v_n_3736_ = lean_nat_sub(v_i_3725_, v_one_3735_);
lean_dec(v_i_3725_);
v___x_3769_ = lean_box(0);
v___x_3770_ = lean_nat_dec_lt(v_n_3736_, v_size_3734_);
if (v___x_3770_ == 0)
{
lean_object* v___x_3771_; 
v___x_3771_ = l_outOfBounds___redArg(v___x_3769_);
v___y_3765_ = v___x_3771_;
goto v___jp_3764_;
}
else
{
lean_object* v___x_3772_; 
v___x_3772_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3769_, v_decls_3733_, v_n_3736_);
v___y_3765_ = v___x_3772_;
goto v___jp_3764_;
}
v___jp_3737_:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Lean_LocalContext_setUserName(v_a_3726_, v___y_3741_, v___y_3740_);
v_i_3725_ = v_n_3736_;
v_a_3726_ = v___x_3742_;
v___y_3727_ = v___y_3738_;
v___y_3728_ = v___y_3739_;
goto _start;
}
v___jp_3744_:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v_fst_3749_; lean_object* v_snd_3750_; lean_object* v_fvarId_3751_; 
lean_inc(v___y_3746_);
v___x_3747_ = l_Lean_NameSet_insert(v___y_3727_, v___y_3746_);
v___x_3748_ = l_Lean_sanitizeName(v___y_3746_, v___y_3728_);
v_fst_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_fst_3749_);
v_snd_3750_ = lean_ctor_get(v___x_3748_, 1);
lean_inc(v_snd_3750_);
lean_dec_ref(v___x_3748_);
v_fvarId_3751_ = lean_ctor_get(v___y_3745_, 1);
lean_inc(v_fvarId_3751_);
lean_dec_ref(v___y_3745_);
v___y_3738_ = v___x_3747_;
v___y_3739_ = v_snd_3750_;
v___y_3740_ = v_fst_3749_;
v___y_3741_ = v_fvarId_3751_;
goto v___jp_3737_;
}
v___jp_3752_:
{
if (v___y_3755_ == 0)
{
lean_object* v___x_3756_; 
lean_dec_ref(v___y_3753_);
v___x_3756_ = l_Lean_NameSet_insert(v___y_3727_, v___y_3754_);
v_i_3725_ = v_n_3736_;
v___y_3727_ = v___x_3756_;
goto _start;
}
else
{
v___y_3745_ = v___y_3753_;
v___y_3746_ = v___y_3754_;
goto v___jp_3744_;
}
}
v___jp_3758_:
{
uint8_t v___x_3761_; 
v___x_3761_ = l_Lean_Name_hasMacroScopes(v___y_3760_);
if (v___x_3761_ == 0)
{
lean_object* v_userName_3762_; uint8_t v___x_3763_; 
v_userName_3762_ = lean_ctor_get(v___y_3759_, 2);
v___x_3763_ = l_Lean_NameSet_contains(v___y_3727_, v_userName_3762_);
v___y_3753_ = v___y_3759_;
v___y_3754_ = v___y_3760_;
v___y_3755_ = v___x_3763_;
goto v___jp_3752_;
}
else
{
v___y_3745_ = v___y_3759_;
v___y_3746_ = v___y_3760_;
goto v___jp_3744_;
}
}
v___jp_3764_:
{
if (lean_obj_tag(v___y_3765_) == 0)
{
v_i_3725_ = v_n_3736_;
goto _start;
}
else
{
lean_object* v_val_3767_; lean_object* v_userName_3768_; 
v_val_3767_ = lean_ctor_get(v___y_3765_, 0);
lean_inc(v_val_3767_);
lean_dec_ref(v___y_3765_);
v_userName_3768_ = lean_ctor_get(v_val_3767_, 2);
lean_inc(v_userName_3768_);
v___y_3759_ = v_val_3767_;
v___y_3760_ = v_userName_3768_;
goto v___jp_3758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v_options_3775_; uint8_t v___x_3776_; 
v_options_3775_ = lean_ctor_get(v_a_3774_, 0);
v___x_3776_ = l_Lean_getSanitizeNames(v_options_3775_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3777_; 
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v_lctx_3773_);
lean_ctor_set(v___x_3777_, 1, v_a_3774_);
return v___x_3777_;
}
else
{
lean_object* v_decls_3778_; lean_object* v_size_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v_fst_3782_; lean_object* v_snd_3783_; lean_object* v_fst_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
v_decls_3778_ = lean_ctor_get(v_lctx_3773_, 1);
v_size_3779_ = lean_ctor_get(v_decls_3778_, 2);
lean_inc(v_size_3779_);
v___x_3780_ = l_Lean_NameSet_empty;
v___x_3781_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3779_, v_lctx_3773_, v___x_3780_, v_a_3774_);
v_fst_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_fst_3782_);
v_snd_3783_ = lean_ctor_get(v___x_3781_, 1);
lean_inc(v_snd_3783_);
lean_dec_ref(v___x_3781_);
v_fst_3784_ = lean_ctor_get(v_fst_3782_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_fst_3782_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; 
v_unused_3792_ = lean_ctor_get(v_fst_3782_, 1);
lean_dec(v_unused_3792_);
v___x_3786_ = v_fst_3782_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_fst_3784_);
lean_dec(v_fst_3782_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 1, v_snd_3783_);
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_fst_3784_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_snd_3783_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3793_, lean_object* v_i_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3794_, v_a_3796_, v___y_3797_, v___y_3798_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3800_, lean_object* v_i_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3800_, v_i_3801_, v_a_3802_, v_a_3803_, v___y_3804_, v___y_3805_);
lean_dec(v_n_3800_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3807_, lean_object* v_fvarId_3808_){
_start:
{
lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___x_3821_; 
lean_inc_ref(v_lctx_3807_);
v___x_3821_ = lean_local_ctx_find(v_lctx_3807_, v_fvarId_3808_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v___x_3822_; 
lean_dec_ref(v_lctx_3807_);
v___x_3822_ = lean_box(0);
return v___x_3822_;
}
else
{
lean_object* v_val_3823_; lean_object* v___y_3825_; lean_object* v_userName_3830_; 
v_val_3823_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_val_3823_);
lean_dec_ref(v___x_3821_);
v_userName_3830_ = lean_ctor_get(v_val_3823_, 2);
lean_inc(v_userName_3830_);
v___y_3825_ = v_userName_3830_;
goto v___jp_3824_;
v___jp_3824_:
{
lean_object* v___x_3826_; 
v___x_3826_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3807_, v___y_3825_);
lean_dec_ref(v_lctx_3807_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v___x_3827_; 
lean_dec(v___y_3825_);
lean_dec(v_val_3823_);
v___x_3827_ = lean_box(0);
return v___x_3827_;
}
else
{
lean_object* v_val_3828_; lean_object* v_fvarId_3829_; 
v_val_3828_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_val_3828_);
lean_dec_ref(v___x_3826_);
v_fvarId_3829_ = lean_ctor_get(v_val_3823_, 1);
lean_inc(v_fvarId_3829_);
lean_dec(v_val_3823_);
v___y_3817_ = v___y_3825_;
v___y_3818_ = v_val_3828_;
v___y_3819_ = v_fvarId_3829_;
goto v___jp_3816_;
}
}
}
v___jp_3809_:
{
uint8_t v___x_3813_; 
v___x_3813_ = l_Lean_instBEqFVarId_beq(v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec(v___y_3811_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; 
lean_dec(v___y_3810_);
v___x_3814_ = lean_box(0);
return v___x_3814_;
}
else
{
lean_object* v___x_3815_; 
v___x_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3815_, 0, v___y_3810_);
return v___x_3815_;
}
}
v___jp_3816_:
{
lean_object* v_fvarId_3820_; 
v_fvarId_3820_ = lean_ctor_get(v___y_3818_, 1);
lean_inc(v_fvarId_3820_);
lean_dec_ref(v___y_3818_);
v___y_3810_ = v___y_3817_;
v___y_3811_ = v___y_3819_;
v___y_3812_ = v_fvarId_3820_;
goto v___jp_3809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3831_, size_t v_i_3832_, lean_object* v_bs_3833_){
_start:
{
uint8_t v___x_3834_; 
v___x_3834_ = lean_usize_dec_lt(v_i_3832_, v_sz_3831_);
if (v___x_3834_ == 0)
{
return v_bs_3833_;
}
else
{
lean_object* v_v_3835_; lean_object* v_snd_3836_; lean_object* v___x_3837_; lean_object* v_bs_x27_3838_; size_t v___x_3839_; size_t v___x_3840_; lean_object* v___x_3841_; 
v_v_3835_ = lean_array_uget_borrowed(v_bs_3833_, v_i_3832_);
v_snd_3836_ = lean_ctor_get(v_v_3835_, 1);
lean_inc(v_snd_3836_);
v___x_3837_ = lean_unsigned_to_nat(0u);
v_bs_x27_3838_ = lean_array_uset(v_bs_3833_, v_i_3832_, v___x_3837_);
v___x_3839_ = ((size_t)1ULL);
v___x_3840_ = lean_usize_add(v_i_3832_, v___x_3839_);
v___x_3841_ = lean_array_uset(v_bs_x27_3838_, v_i_3832_, v_snd_3836_);
v_i_3832_ = v___x_3840_;
v_bs_3833_ = v___x_3841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3843_, lean_object* v_i_3844_, lean_object* v_bs_3845_){
_start:
{
size_t v_sz_boxed_3846_; size_t v_i_boxed_3847_; lean_object* v_res_3848_; 
v_sz_boxed_3846_ = lean_unbox_usize(v_sz_3843_);
lean_dec(v_sz_3843_);
v_i_boxed_3847_ = lean_unbox_usize(v_i_3844_);
lean_dec(v_i_3844_);
v_res_3848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3846_, v_i_boxed_3847_, v_bs_3845_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3849_, size_t v_sz_3850_, size_t v_i_3851_, lean_object* v_bs_3852_){
_start:
{
uint8_t v___x_3853_; 
v___x_3853_ = lean_usize_dec_lt(v_i_3851_, v_sz_3850_);
if (v___x_3853_ == 0)
{
return v_bs_3852_;
}
else
{
lean_object* v_fvarIdToDecl_3854_; lean_object* v_v_3855_; lean_object* v___x_3856_; lean_object* v_bs_x27_3857_; lean_object* v___y_3859_; lean_object* v___x_3864_; 
v_fvarIdToDecl_3854_ = lean_ctor_get(v_lctx_3849_, 0);
v_v_3855_ = lean_array_uget(v_bs_3852_, v_i_3851_);
v___x_3856_ = lean_unsigned_to_nat(0u);
v_bs_x27_3857_ = lean_array_uset(v_bs_3852_, v_i_3851_, v___x_3856_);
v___x_3864_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3854_, v_v_3855_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3856_);
lean_ctor_set(v___x_3865_, 1, v_v_3855_);
v___y_3859_ = v___x_3865_;
goto v___jp_3858_;
}
else
{
lean_object* v_val_3866_; lean_object* v_index_3867_; lean_object* v___x_3868_; 
v_val_3866_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_val_3866_);
lean_dec_ref(v___x_3864_);
v_index_3867_ = lean_ctor_get(v_val_3866_, 0);
lean_inc(v_index_3867_);
lean_dec(v_val_3866_);
v___x_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3868_, 0, v_index_3867_);
lean_ctor_set(v___x_3868_, 1, v_v_3855_);
v___y_3859_ = v___x_3868_;
goto v___jp_3858_;
}
v___jp_3858_:
{
size_t v___x_3860_; size_t v___x_3861_; lean_object* v___x_3862_; 
v___x_3860_ = ((size_t)1ULL);
v___x_3861_ = lean_usize_add(v_i_3851_, v___x_3860_);
v___x_3862_ = lean_array_uset(v_bs_x27_3857_, v_i_3851_, v___y_3859_);
v_i_3851_ = v___x_3861_;
v_bs_3852_ = v___x_3862_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3869_, lean_object* v_sz_3870_, lean_object* v_i_3871_, lean_object* v_bs_3872_){
_start:
{
size_t v_sz_boxed_3873_; size_t v_i_boxed_3874_; lean_object* v_res_3875_; 
v_sz_boxed_3873_ = lean_unbox_usize(v_sz_3870_);
lean_dec(v_sz_3870_);
v_i_boxed_3874_ = lean_unbox_usize(v_i_3871_);
lean_dec(v_i_3871_);
v_res_3875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3869_, v_sz_boxed_3873_, v_i_boxed_3874_, v_bs_3872_);
lean_dec_ref(v_lctx_3869_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object* v_hi_3876_, lean_object* v_pivot_3877_, lean_object* v_as_3878_, lean_object* v_i_3879_, lean_object* v_k_3880_){
_start:
{
uint8_t v___x_3881_; 
v___x_3881_ = lean_nat_dec_lt(v_k_3880_, v_hi_3876_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
lean_dec(v_k_3880_);
v___x_3882_ = lean_array_fswap(v_as_3878_, v_i_3879_, v_hi_3876_);
v___x_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3883_, 0, v_i_3879_);
lean_ctor_set(v___x_3883_, 1, v___x_3882_);
return v___x_3883_;
}
else
{
lean_object* v___x_3884_; lean_object* v_fst_3885_; lean_object* v_fst_3886_; uint8_t v___x_3887_; 
v___x_3884_ = lean_array_fget_borrowed(v_as_3878_, v_k_3880_);
v_fst_3885_ = lean_ctor_get(v___x_3884_, 0);
v_fst_3886_ = lean_ctor_get(v_pivot_3877_, 0);
v___x_3887_ = lean_nat_dec_lt(v_fst_3885_, v_fst_3886_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = lean_unsigned_to_nat(1u);
v___x_3889_ = lean_nat_add(v_k_3880_, v___x_3888_);
lean_dec(v_k_3880_);
v_k_3880_ = v___x_3889_;
goto _start;
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3891_ = lean_array_fswap(v_as_3878_, v_i_3879_, v_k_3880_);
v___x_3892_ = lean_unsigned_to_nat(1u);
v___x_3893_ = lean_nat_add(v_i_3879_, v___x_3892_);
lean_dec(v_i_3879_);
v___x_3894_ = lean_nat_add(v_k_3880_, v___x_3892_);
lean_dec(v_k_3880_);
v_as_3878_ = v___x_3891_;
v_i_3879_ = v___x_3893_;
v_k_3880_ = v___x_3894_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object* v_hi_3896_, lean_object* v_pivot_3897_, lean_object* v_as_3898_, lean_object* v_i_3899_, lean_object* v_k_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3896_, v_pivot_3897_, v_as_3898_, v_i_3899_, v_k_3900_);
lean_dec_ref(v_pivot_3897_);
lean_dec(v_hi_3896_);
return v_res_3901_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3902_, lean_object* v_i_3903_){
_start:
{
lean_object* v_fst_3904_; lean_object* v_fst_3905_; uint8_t v___x_3906_; 
v_fst_3904_ = lean_ctor_get(v_h_3902_, 0);
v_fst_3905_ = lean_ctor_get(v_i_3903_, 0);
v___x_3906_ = lean_nat_dec_lt(v_fst_3904_, v_fst_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3907_, lean_object* v_i_3908_){
_start:
{
uint8_t v_res_3909_; lean_object* v_r_3910_; 
v_res_3909_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3907_, v_i_3908_);
lean_dec_ref(v_i_3908_);
lean_dec_ref(v_h_3907_);
v_r_3910_ = lean_box(v_res_3909_);
return v_r_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_n_3911_, lean_object* v_as_3912_, lean_object* v_lo_3913_, lean_object* v_hi_3914_){
_start:
{
lean_object* v___y_3916_; uint8_t v___x_3926_; 
v___x_3926_ = lean_nat_dec_lt(v_lo_3913_, v_hi_3914_);
if (v___x_3926_ == 0)
{
lean_dec(v_lo_3913_);
return v_as_3912_;
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v_mid_3929_; lean_object* v___y_3931_; lean_object* v___y_3937_; lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; 
v___x_3927_ = lean_nat_add(v_lo_3913_, v_hi_3914_);
v___x_3928_ = lean_unsigned_to_nat(1u);
v_mid_3929_ = lean_nat_shiftr(v___x_3927_, v___x_3928_);
lean_dec(v___x_3927_);
v___x_3942_ = lean_array_fget_borrowed(v_as_3912_, v_mid_3929_);
v___x_3943_ = lean_array_fget_borrowed(v_as_3912_, v_lo_3913_);
v___x_3944_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3942_, v___x_3943_);
if (v___x_3944_ == 0)
{
v___y_3937_ = v_as_3912_;
goto v___jp_3936_;
}
else
{
lean_object* v___x_3945_; 
v___x_3945_ = lean_array_fswap(v_as_3912_, v_lo_3913_, v_mid_3929_);
v___y_3937_ = v___x_3945_;
goto v___jp_3936_;
}
v___jp_3930_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; uint8_t v___x_3934_; 
v___x_3932_ = lean_array_fget_borrowed(v___y_3931_, v_mid_3929_);
v___x_3933_ = lean_array_fget_borrowed(v___y_3931_, v_hi_3914_);
v___x_3934_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3932_, v___x_3933_);
if (v___x_3934_ == 0)
{
lean_dec(v_mid_3929_);
v___y_3916_ = v___y_3931_;
goto v___jp_3915_;
}
else
{
lean_object* v___x_3935_; 
v___x_3935_ = lean_array_fswap(v___y_3931_, v_mid_3929_, v_hi_3914_);
lean_dec(v_mid_3929_);
v___y_3916_ = v___x_3935_;
goto v___jp_3915_;
}
}
v___jp_3936_:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; uint8_t v___x_3940_; 
v___x_3938_ = lean_array_fget_borrowed(v___y_3937_, v_hi_3914_);
v___x_3939_ = lean_array_fget_borrowed(v___y_3937_, v_lo_3913_);
v___x_3940_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3938_, v___x_3939_);
if (v___x_3940_ == 0)
{
v___y_3931_ = v___y_3937_;
goto v___jp_3930_;
}
else
{
lean_object* v___x_3941_; 
v___x_3941_ = lean_array_fswap(v___y_3937_, v_lo_3913_, v_hi_3914_);
v___y_3931_ = v___x_3941_;
goto v___jp_3930_;
}
}
}
v___jp_3915_:
{
lean_object* v_pivot_3917_; lean_object* v___x_3918_; lean_object* v_fst_3919_; lean_object* v_snd_3920_; uint8_t v___x_3921_; 
v_pivot_3917_ = lean_array_fget(v___y_3916_, v_hi_3914_);
lean_inc_n(v_lo_3913_, 2);
v___x_3918_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3914_, v_pivot_3917_, v___y_3916_, v_lo_3913_, v_lo_3913_);
lean_dec(v_pivot_3917_);
v_fst_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_fst_3919_);
v_snd_3920_ = lean_ctor_get(v___x_3918_, 1);
lean_inc(v_snd_3920_);
lean_dec_ref(v___x_3918_);
v___x_3921_ = lean_nat_dec_le(v_hi_3914_, v_fst_3919_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3922_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3911_, v_snd_3920_, v_lo_3913_, v_fst_3919_);
v___x_3923_ = lean_unsigned_to_nat(1u);
v___x_3924_ = lean_nat_add(v_fst_3919_, v___x_3923_);
lean_dec(v_fst_3919_);
v_as_3912_ = v___x_3922_;
v_lo_3913_ = v___x_3924_;
goto _start;
}
else
{
lean_dec(v_fst_3919_);
lean_dec(v_lo_3913_);
return v_snd_3920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_n_3946_, lean_object* v_as_3947_, lean_object* v_lo_3948_, lean_object* v_hi_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3946_, v_as_3947_, v_lo_3948_, v_hi_3949_);
lean_dec(v_hi_3949_);
lean_dec(v_n_3946_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3951_, lean_object* v_hyps_3952_){
_start:
{
lean_object* v___y_3954_; size_t v_sz_3958_; size_t v___x_3959_; lean_object* v_hyps_3960_; lean_object* v___x_3961_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v_sz_3958_ = lean_array_size(v_hyps_3952_);
v___x_3959_ = ((size_t)0ULL);
v_hyps_3960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3951_, v_sz_3958_, v___x_3959_, v_hyps_3952_);
v___x_3961_ = lean_array_get_size(v_hyps_3960_);
v___x_3966_ = lean_unsigned_to_nat(0u);
v___x_3967_ = lean_nat_dec_eq(v___x_3961_, v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___y_3971_; uint8_t v___x_3973_; 
v___x_3968_ = lean_unsigned_to_nat(1u);
v___x_3969_ = lean_nat_sub(v___x_3961_, v___x_3968_);
v___x_3973_ = lean_nat_dec_le(v___x_3966_, v___x_3969_);
if (v___x_3973_ == 0)
{
lean_inc(v___x_3969_);
v___y_3971_ = v___x_3969_;
goto v___jp_3970_;
}
else
{
v___y_3971_ = v___x_3966_;
goto v___jp_3970_;
}
v___jp_3970_:
{
uint8_t v___x_3972_; 
v___x_3972_ = lean_nat_dec_le(v___y_3971_, v___x_3969_);
if (v___x_3972_ == 0)
{
lean_dec(v___x_3969_);
lean_inc(v___y_3971_);
v___y_3963_ = v___y_3971_;
v___y_3964_ = v___y_3971_;
goto v___jp_3962_;
}
else
{
v___y_3963_ = v___y_3971_;
v___y_3964_ = v___x_3969_;
goto v___jp_3962_;
}
}
}
else
{
v___y_3954_ = v_hyps_3960_;
goto v___jp_3953_;
}
v___jp_3953_:
{
size_t v_sz_3955_; size_t v___x_3956_; lean_object* v___x_3957_; 
v_sz_3955_ = lean_array_size(v___y_3954_);
v___x_3956_ = ((size_t)0ULL);
v___x_3957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3955_, v___x_3956_, v___y_3954_);
return v___x_3957_;
}
v___jp_3962_:
{
lean_object* v___x_3965_; 
v___x_3965_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v___x_3961_, v_hyps_3960_, v___y_3963_, v___y_3964_);
lean_dec(v___y_3964_);
v___y_3954_ = v___x_3965_;
goto v___jp_3953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object* v_lctx_3974_, lean_object* v_hyps_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_3974_, v_hyps_3975_);
lean_dec_ref(v_lctx_3974_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_3977_, lean_object* v_as_3978_, lean_object* v_lo_3979_, lean_object* v_hi_3980_, lean_object* v_w_3981_, lean_object* v_hlo_3982_, lean_object* v_hhi_3983_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3977_, v_as_3978_, v_lo_3979_, v_hi_3980_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_3985_, lean_object* v_as_3986_, lean_object* v_lo_3987_, lean_object* v_hi_3988_, lean_object* v_w_3989_, lean_object* v_hlo_3990_, lean_object* v_hhi_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_3985_, v_as_3986_, v_lo_3987_, v_hi_3988_, v_w_3989_, v_hlo_3990_, v_hhi_3991_);
lean_dec(v_hi_3988_);
lean_dec(v_n_3985_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object* v_n_3993_, lean_object* v_lo_3994_, lean_object* v_hi_3995_, lean_object* v_hhi_3996_, lean_object* v_pivot_3997_, lean_object* v_as_3998_, lean_object* v_i_3999_, lean_object* v_k_4000_, lean_object* v_ilo_4001_, lean_object* v_ik_4002_, lean_object* v_w_4003_){
_start:
{
lean_object* v___x_4004_; 
v___x_4004_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3995_, v_pivot_3997_, v_as_3998_, v_i_3999_, v_k_4000_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object* v_n_4005_, lean_object* v_lo_4006_, lean_object* v_hi_4007_, lean_object* v_hhi_4008_, lean_object* v_pivot_4009_, lean_object* v_as_4010_, lean_object* v_i_4011_, lean_object* v_k_4012_, lean_object* v_ilo_4013_, lean_object* v_ik_4014_, lean_object* v_w_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(v_n_4005_, v_lo_4006_, v_hi_4007_, v_hhi_4008_, v_pivot_4009_, v_as_4010_, v_i_4011_, v_k_4012_, v_ilo_4013_, v_ik_4014_, v_w_4015_);
lean_dec_ref(v_pivot_4009_);
lean_dec(v_hi_4007_);
lean_dec(v_lo_4006_);
lean_dec(v_n_4005_);
return v_res_4016_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_4017_, lean_object* v_x_4018_){
_start:
{
if (lean_obj_tag(v_x_4018_) == 0)
{
uint8_t v___x_4019_; 
v___x_4019_ = 0;
return v___x_4019_;
}
else
{
lean_object* v_key_4020_; lean_object* v_tail_4021_; uint8_t v___x_4022_; 
v_key_4020_ = lean_ctor_get(v_x_4018_, 0);
v_tail_4021_ = lean_ctor_get(v_x_4018_, 2);
v___x_4022_ = lean_name_eq(v_key_4020_, v_a_4017_);
if (v___x_4022_ == 0)
{
v_x_4018_ = v_tail_4021_;
goto _start;
}
else
{
return v___x_4022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_4024_, lean_object* v_x_4025_){
_start:
{
uint8_t v_res_4026_; lean_object* v_r_4027_; 
v_res_4026_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4024_, v_x_4025_);
lean_dec(v_x_4025_);
lean_dec(v_a_4024_);
v_r_4027_ = lean_box(v_res_4026_);
return v_r_4027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_4028_, lean_object* v_x_4029_){
_start:
{
if (lean_obj_tag(v_x_4029_) == 0)
{
return v_x_4029_;
}
else
{
lean_object* v_key_4030_; lean_object* v_value_4031_; lean_object* v_tail_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4041_; 
v_key_4030_ = lean_ctor_get(v_x_4029_, 0);
v_value_4031_ = lean_ctor_get(v_x_4029_, 1);
v_tail_4032_ = lean_ctor_get(v_x_4029_, 2);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_x_4029_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4034_ = v_x_4029_;
v_isShared_4035_ = v_isSharedCheck_4041_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_tail_4032_);
lean_inc(v_value_4031_);
lean_inc(v_key_4030_);
lean_dec(v_x_4029_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4041_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
uint8_t v___x_4036_; 
v___x_4036_ = lean_name_eq(v_key_4030_, v_a_4028_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; lean_object* v___x_4039_; 
v___x_4037_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4028_, v_tail_4032_);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 2, v___x_4037_);
v___x_4039_ = v___x_4034_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_key_4030_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_value_4031_);
lean_ctor_set(v_reuseFailAlloc_4040_, 2, v___x_4037_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
else
{
lean_del_object(v___x_4034_);
lean_dec(v_value_4031_);
lean_dec(v_key_4030_);
return v_tail_4032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_4042_, lean_object* v_x_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4042_, v_x_4043_);
lean_dec(v_a_4042_);
return v_res_4044_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4045_; uint64_t v___x_4046_; 
v___x_4045_ = lean_unsigned_to_nat(1723u);
v___x_4046_ = lean_uint64_of_nat(v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v_size_4049_; lean_object* v_buckets_4050_; lean_object* v___x_4051_; uint64_t v___y_4053_; 
v_size_4049_ = lean_ctor_get(v_m_4047_, 0);
v_buckets_4050_ = lean_ctor_get(v_m_4047_, 1);
v___x_4051_ = lean_array_get_size(v_buckets_4050_);
if (lean_obj_tag(v_a_4048_) == 0)
{
uint64_t v___x_4082_; 
v___x_4082_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_4053_ = v___x_4082_;
goto v___jp_4052_;
}
else
{
uint64_t v_hash_4083_; 
v_hash_4083_ = lean_ctor_get_uint64(v_a_4048_, sizeof(void*)*2);
v___y_4053_ = v_hash_4083_;
goto v___jp_4052_;
}
v___jp_4052_:
{
uint64_t v___x_4054_; uint64_t v___x_4055_; uint64_t v_fold_4056_; uint64_t v___x_4057_; uint64_t v___x_4058_; uint64_t v___x_4059_; size_t v___x_4060_; size_t v___x_4061_; size_t v___x_4062_; size_t v___x_4063_; size_t v___x_4064_; lean_object* v_bkt_4065_; uint8_t v___x_4066_; 
v___x_4054_ = 32ULL;
v___x_4055_ = lean_uint64_shift_right(v___y_4053_, v___x_4054_);
v_fold_4056_ = lean_uint64_xor(v___y_4053_, v___x_4055_);
v___x_4057_ = 16ULL;
v___x_4058_ = lean_uint64_shift_right(v_fold_4056_, v___x_4057_);
v___x_4059_ = lean_uint64_xor(v_fold_4056_, v___x_4058_);
v___x_4060_ = lean_uint64_to_usize(v___x_4059_);
v___x_4061_ = lean_usize_of_nat(v___x_4051_);
v___x_4062_ = ((size_t)1ULL);
v___x_4063_ = lean_usize_sub(v___x_4061_, v___x_4062_);
v___x_4064_ = lean_usize_land(v___x_4060_, v___x_4063_);
v_bkt_4065_ = lean_array_uget_borrowed(v_buckets_4050_, v___x_4064_);
v___x_4066_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4048_, v_bkt_4065_);
if (v___x_4066_ == 0)
{
return v_m_4047_;
}
else
{
lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4079_; 
lean_inc(v_bkt_4065_);
lean_inc_ref(v_buckets_4050_);
lean_inc(v_size_4049_);
v_isSharedCheck_4079_ = !lean_is_exclusive(v_m_4047_);
if (v_isSharedCheck_4079_ == 0)
{
lean_object* v_unused_4080_; lean_object* v_unused_4081_; 
v_unused_4080_ = lean_ctor_get(v_m_4047_, 1);
lean_dec(v_unused_4080_);
v_unused_4081_ = lean_ctor_get(v_m_4047_, 0);
lean_dec(v_unused_4081_);
v___x_4068_ = v_m_4047_;
v_isShared_4069_ = v_isSharedCheck_4079_;
goto v_resetjp_4067_;
}
else
{
lean_dec(v_m_4047_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4079_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4070_; lean_object* v_buckets_x27_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4077_; 
v___x_4070_ = lean_box(0);
v_buckets_x27_4071_ = lean_array_uset(v_buckets_4050_, v___x_4064_, v___x_4070_);
v___x_4072_ = lean_unsigned_to_nat(1u);
v___x_4073_ = lean_nat_sub(v_size_4049_, v___x_4072_);
lean_dec(v_size_4049_);
v___x_4074_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4048_, v_bkt_4065_);
v___x_4075_ = lean_array_uset(v_buckets_x27_4071_, v___x_4064_, v___x_4074_);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 1, v___x_4075_);
lean_ctor_set(v___x_4068_, 0, v___x_4073_);
v___x_4077_ = v___x_4068_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v___x_4075_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4084_, v_a_4085_);
lean_dec(v_a_4085_);
return v_res_4086_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v_buckets_4089_; lean_object* v___x_4090_; uint64_t v___y_4092_; 
v_buckets_4089_ = lean_ctor_get(v_m_4087_, 1);
v___x_4090_ = lean_array_get_size(v_buckets_4089_);
if (lean_obj_tag(v_a_4088_) == 0)
{
uint64_t v___x_4106_; 
v___x_4106_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_4092_ = v___x_4106_;
goto v___jp_4091_;
}
else
{
uint64_t v_hash_4107_; 
v_hash_4107_ = lean_ctor_get_uint64(v_a_4088_, sizeof(void*)*2);
v___y_4092_ = v_hash_4107_;
goto v___jp_4091_;
}
v___jp_4091_:
{
uint64_t v___x_4093_; uint64_t v___x_4094_; uint64_t v_fold_4095_; uint64_t v___x_4096_; uint64_t v___x_4097_; uint64_t v___x_4098_; size_t v___x_4099_; size_t v___x_4100_; size_t v___x_4101_; size_t v___x_4102_; size_t v___x_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
v___x_4093_ = 32ULL;
v___x_4094_ = lean_uint64_shift_right(v___y_4092_, v___x_4093_);
v_fold_4095_ = lean_uint64_xor(v___y_4092_, v___x_4094_);
v___x_4096_ = 16ULL;
v___x_4097_ = lean_uint64_shift_right(v_fold_4095_, v___x_4096_);
v___x_4098_ = lean_uint64_xor(v_fold_4095_, v___x_4097_);
v___x_4099_ = lean_uint64_to_usize(v___x_4098_);
v___x_4100_ = lean_usize_of_nat(v___x_4090_);
v___x_4101_ = ((size_t)1ULL);
v___x_4102_ = lean_usize_sub(v___x_4100_, v___x_4101_);
v___x_4103_ = lean_usize_land(v___x_4099_, v___x_4102_);
v___x_4104_ = lean_array_uget_borrowed(v_buckets_4089_, v___x_4103_);
v___x_4105_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4088_, v___x_4104_);
return v___x_4105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4108_, lean_object* v_a_4109_){
_start:
{
uint8_t v_res_4110_; lean_object* v_r_4111_; 
v_res_4110_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4108_, v_a_4109_);
lean_dec(v_a_4109_);
lean_dec_ref(v_m_4108_);
v_r_4111_ = lean_box(v_res_4110_);
return v_r_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4112_, lean_object* v_as_4113_, size_t v_i_4114_, size_t v_stop_4115_, lean_object* v_b_4116_){
_start:
{
uint8_t v___x_4117_; 
v___x_4117_ = lean_usize_dec_eq(v_i_4114_, v_stop_4115_);
if (v___x_4117_ == 0)
{
size_t v___x_4118_; size_t v___x_4119_; lean_object* v___x_4120_; 
v___x_4118_ = ((size_t)1ULL);
v___x_4119_ = lean_usize_sub(v_i_4114_, v___x_4118_);
v___x_4120_ = lean_array_uget(v_as_4113_, v___x_4119_);
if (lean_obj_tag(v___x_4120_) == 0)
{
v_i_4114_ = v___x_4119_;
goto _start;
}
else
{
lean_object* v_val_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4156_; 
v_val_4122_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4124_ = v___x_4120_;
v_isShared_4125_ = v_isSharedCheck_4156_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_val_4122_);
lean_dec(v___x_4120_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4156_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v_fst_4126_; lean_object* v_snd_4127_; lean_object* v___y_4129_; lean_object* v___y_4145_; lean_object* v_size_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
v_fst_4126_ = lean_ctor_get(v_b_4116_, 0);
v_snd_4127_ = lean_ctor_get(v_b_4116_, 1);
v_size_4151_ = lean_ctor_get(v_fst_4126_, 0);
v___x_4152_ = lean_unsigned_to_nat(0u);
v___x_4153_ = lean_nat_dec_eq(v_size_4151_, v___x_4152_);
if (v___x_4153_ == 0)
{
lean_object* v_index_4154_; 
v_index_4154_ = lean_ctor_get(v_val_4122_, 0);
lean_inc(v_index_4154_);
v___y_4145_ = v_index_4154_;
goto v___jp_4144_;
}
else
{
lean_object* v___x_4155_; 
lean_inc(v_snd_4127_);
lean_del_object(v___x_4124_);
lean_dec(v_val_4122_);
lean_dec_ref(v_b_4116_);
v___x_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4155_, 0, v_snd_4127_);
return v___x_4155_;
}
v___jp_4128_:
{
uint8_t v___x_4130_; 
v___x_4130_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4126_, v___y_4129_);
if (v___x_4130_ == 0)
{
lean_dec(v___y_4129_);
lean_dec(v_val_4122_);
v_i_4114_ = v___x_4119_;
goto _start;
}
else
{
lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4141_; 
lean_inc(v_snd_4127_);
lean_inc(v_fst_4126_);
v_isSharedCheck_4141_ = !lean_is_exclusive(v_b_4116_);
if (v_isSharedCheck_4141_ == 0)
{
lean_object* v_unused_4142_; lean_object* v_unused_4143_; 
v_unused_4142_ = lean_ctor_get(v_b_4116_, 1);
lean_dec(v_unused_4142_);
v_unused_4143_ = lean_ctor_get(v_b_4116_, 0);
lean_dec(v_unused_4143_);
v___x_4133_ = v_b_4116_;
v_isShared_4134_ = v_isSharedCheck_4141_;
goto v_resetjp_4132_;
}
else
{
lean_dec(v_b_4116_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4141_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
v___x_4135_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4126_, v___y_4129_);
lean_dec(v___y_4129_);
v___x_4136_ = lean_array_push(v_snd_4127_, v_val_4122_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 1, v___x_4136_);
lean_ctor_set(v___x_4133_, 0, v___x_4135_);
v___x_4138_ = v___x_4133_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4135_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
v_i_4114_ = v___x_4119_;
v_b_4116_ = v___x_4138_;
goto _start;
}
}
}
}
v___jp_4144_:
{
uint8_t v___x_4146_; 
v___x_4146_ = lean_nat_dec_lt(v___y_4145_, v_start_4112_);
lean_dec(v___y_4145_);
if (v___x_4146_ == 0)
{
lean_object* v_userName_4147_; 
lean_del_object(v___x_4124_);
v_userName_4147_ = lean_ctor_get(v_val_4122_, 2);
lean_inc(v_userName_4147_);
v___y_4129_ = v_userName_4147_;
goto v___jp_4128_;
}
else
{
lean_object* v___x_4149_; 
lean_inc(v_snd_4127_);
lean_dec(v_val_4122_);
lean_dec_ref(v_b_4116_);
if (v_isShared_4125_ == 0)
{
lean_ctor_set_tag(v___x_4124_, 0);
lean_ctor_set(v___x_4124_, 0, v_snd_4127_);
v___x_4149_ = v___x_4124_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_snd_4127_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
}
}
else
{
lean_object* v___x_4157_; 
v___x_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4157_, 0, v_b_4116_);
return v___x_4157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4158_, lean_object* v_as_4159_, lean_object* v_i_4160_, lean_object* v_stop_4161_, lean_object* v_b_4162_){
_start:
{
size_t v_i_boxed_4163_; size_t v_stop_boxed_4164_; lean_object* v_res_4165_; 
v_i_boxed_4163_ = lean_unbox_usize(v_i_4160_);
lean_dec(v_i_4160_);
v_stop_boxed_4164_ = lean_unbox_usize(v_stop_4161_);
lean_dec(v_stop_4161_);
v_res_4165_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4158_, v_as_4159_, v_i_boxed_4163_, v_stop_boxed_4164_, v_b_4162_);
lean_dec_ref(v_as_4159_);
lean_dec(v_start_4158_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4166_, lean_object* v_x_4167_, lean_object* v_x_4168_){
_start:
{
if (lean_obj_tag(v_x_4167_) == 0)
{
lean_object* v_cs_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4182_; 
v_cs_4169_ = lean_ctor_get(v_x_4167_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v_x_4167_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4171_ = v_x_4167_;
v_isShared_4172_ = v_isSharedCheck_4182_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_cs_4169_);
lean_dec(v_x_4167_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4182_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; uint8_t v___x_4175_; 
v___x_4173_ = lean_array_get_size(v_cs_4169_);
v___x_4174_ = lean_unsigned_to_nat(0u);
v___x_4175_ = lean_nat_dec_lt(v___x_4174_, v___x_4173_);
if (v___x_4175_ == 0)
{
lean_object* v___x_4177_; 
lean_dec_ref(v_cs_4169_);
if (v_isShared_4172_ == 0)
{
lean_ctor_set_tag(v___x_4171_, 1);
lean_ctor_set(v___x_4171_, 0, v_x_4168_);
v___x_4177_ = v___x_4171_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_x_4168_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
else
{
size_t v___x_4179_; size_t v___x_4180_; lean_object* v___x_4181_; 
lean_del_object(v___x_4171_);
v___x_4179_ = lean_usize_of_nat(v___x_4173_);
v___x_4180_ = ((size_t)0ULL);
v___x_4181_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4166_, v_cs_4169_, v___x_4179_, v___x_4180_, v_x_4168_);
lean_dec_ref(v_cs_4169_);
return v___x_4181_;
}
}
}
else
{
lean_object* v_vs_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4196_; 
v_vs_4183_ = lean_ctor_get(v_x_4167_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v_x_4167_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4185_ = v_x_4167_;
v_isShared_4186_ = v_isSharedCheck_4196_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_vs_4183_);
lean_dec(v_x_4167_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4196_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; 
v___x_4187_ = lean_array_get_size(v_vs_4183_);
v___x_4188_ = lean_unsigned_to_nat(0u);
v___x_4189_ = lean_nat_dec_lt(v___x_4188_, v___x_4187_);
if (v___x_4189_ == 0)
{
lean_object* v___x_4191_; 
lean_dec_ref(v_vs_4183_);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 0, v_x_4168_);
v___x_4191_ = v___x_4185_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_x_4168_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
else
{
size_t v___x_4193_; size_t v___x_4194_; lean_object* v___x_4195_; 
lean_del_object(v___x_4185_);
v___x_4193_ = lean_usize_of_nat(v___x_4187_);
v___x_4194_ = ((size_t)0ULL);
v___x_4195_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4166_, v_vs_4183_, v___x_4193_, v___x_4194_, v_x_4168_);
lean_dec_ref(v_vs_4183_);
return v___x_4195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4197_, lean_object* v_as_4198_, size_t v_i_4199_, size_t v_stop_4200_, lean_object* v_b_4201_){
_start:
{
uint8_t v___x_4202_; 
v___x_4202_ = lean_usize_dec_eq(v_i_4199_, v_stop_4200_);
if (v___x_4202_ == 0)
{
size_t v___x_4203_; size_t v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4203_ = ((size_t)1ULL);
v___x_4204_ = lean_usize_sub(v_i_4199_, v___x_4203_);
v___x_4205_ = lean_array_uget_borrowed(v_as_4198_, v___x_4204_);
lean_inc(v___x_4205_);
v___x_4206_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4197_, v___x_4205_, v_b_4201_);
if (lean_obj_tag(v___x_4206_) == 0)
{
return v___x_4206_;
}
else
{
lean_object* v_a_4207_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_a_4207_);
lean_dec_ref(v___x_4206_);
v_i_4199_ = v___x_4204_;
v_b_4201_ = v_a_4207_;
goto _start;
}
}
else
{
lean_object* v___x_4209_; 
v___x_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4209_, 0, v_b_4201_);
return v___x_4209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4210_, lean_object* v_as_4211_, lean_object* v_i_4212_, lean_object* v_stop_4213_, lean_object* v_b_4214_){
_start:
{
size_t v_i_boxed_4215_; size_t v_stop_boxed_4216_; lean_object* v_res_4217_; 
v_i_boxed_4215_ = lean_unbox_usize(v_i_4212_);
lean_dec(v_i_4212_);
v_stop_boxed_4216_ = lean_unbox_usize(v_stop_4213_);
lean_dec(v_stop_4213_);
v_res_4217_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4210_, v_as_4211_, v_i_boxed_4215_, v_stop_boxed_4216_, v_b_4214_);
lean_dec_ref(v_as_4211_);
lean_dec(v_start_4210_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4218_, lean_object* v_x_4219_, lean_object* v_x_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4218_, v_x_4219_, v_x_4220_);
lean_dec(v_start_4218_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4222_, lean_object* v_t_4223_, lean_object* v_init_4224_){
_start:
{
lean_object* v_root_4225_; lean_object* v_tail_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; uint8_t v___x_4229_; 
v_root_4225_ = lean_ctor_get(v_t_4223_, 0);
lean_inc_ref(v_root_4225_);
v_tail_4226_ = lean_ctor_get(v_t_4223_, 1);
lean_inc_ref(v_tail_4226_);
lean_dec_ref(v_t_4223_);
v___x_4227_ = lean_array_get_size(v_tail_4226_);
v___x_4228_ = lean_unsigned_to_nat(0u);
v___x_4229_ = lean_nat_dec_lt(v___x_4228_, v___x_4227_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; 
lean_dec_ref(v_tail_4226_);
v___x_4230_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4222_, v_root_4225_, v_init_4224_);
return v___x_4230_;
}
else
{
size_t v___x_4231_; size_t v___x_4232_; lean_object* v___x_4233_; 
v___x_4231_ = lean_usize_of_nat(v___x_4227_);
v___x_4232_ = ((size_t)0ULL);
v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4222_, v_tail_4226_, v___x_4231_, v___x_4232_, v_init_4224_);
lean_dec_ref(v_tail_4226_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_dec_ref(v_root_4225_);
return v___x_4233_;
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4235_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref(v___x_4233_);
v___x_4235_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4222_, v_root_4225_, v_a_4234_);
return v___x_4235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4236_, lean_object* v_t_4237_, lean_object* v_init_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4236_, v_t_4237_, v_init_4238_);
lean_dec(v_start_4236_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4240_, lean_object* v_lctx_4241_, lean_object* v_init_4242_){
_start:
{
lean_object* v_decls_4243_; lean_object* v___x_4244_; 
v_decls_4243_ = lean_ctor_get(v_lctx_4241_, 1);
lean_inc_ref(v_decls_4243_);
lean_dec_ref(v_lctx_4241_);
v___x_4244_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4240_, v_decls_4243_, v_init_4242_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4245_, lean_object* v_lctx_4246_, lean_object* v_init_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4245_, v_lctx_4246_, v_init_4247_);
lean_dec(v_start_4245_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4251_, lean_object* v_userNames_4252_, lean_object* v_start_4253_){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4254_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4255_, 0, v_userNames_4252_);
lean_ctor_set(v___x_4255_, 1, v___x_4254_);
v___x_4256_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4253_, v_lctx_4251_, v___x_4255_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4258_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref(v___x_4256_);
v___x_4258_ = l_Array_reverse___redArg(v_a_4257_);
return v___x_4258_;
}
else
{
lean_object* v_a_4259_; lean_object* v_snd_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v_a_4259_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4259_);
lean_dec_ref(v___x_4256_);
v_snd_4260_ = lean_ctor_get(v_a_4259_, 1);
lean_inc(v_snd_4260_);
lean_dec(v_a_4259_);
v___x_4261_ = l_Array_reverse___redArg(v_snd_4260_);
v___x_4262_ = l_Array_reverse___redArg(v___x_4261_);
return v___x_4262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4263_, lean_object* v_userNames_4264_, lean_object* v_start_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4263_, v_userNames_4264_, v_start_4265_);
lean_dec(v_start_4265_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4267_, lean_object* v_lctx_4268_, lean_object* v_userNames_4269_, lean_object* v_start_4270_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4268_, v_userNames_4269_, v_start_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4272_, lean_object* v_lctx_4273_, lean_object* v_userNames_4274_, lean_object* v_start_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4272_, v_lctx_4273_, v_userNames_4274_, v_start_4275_);
lean_dec(v_start_4275_);
return v_res_4276_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4277_, lean_object* v_m_4278_, lean_object* v_a_4279_){
_start:
{
uint8_t v___x_4280_; 
v___x_4280_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4278_, v_a_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4281_, lean_object* v_m_4282_, lean_object* v_a_4283_){
_start:
{
uint8_t v_res_4284_; lean_object* v_r_4285_; 
v_res_4284_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4281_, v_m_4282_, v_a_4283_);
lean_dec(v_a_4283_);
lean_dec_ref(v_m_4282_);
v_r_4285_ = lean_box(v_res_4284_);
return v_r_4285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4286_, lean_object* v_m_4287_, lean_object* v_a_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4287_, v_a_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4290_, lean_object* v_m_4291_, lean_object* v_a_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4290_, v_m_4291_, v_a_4292_);
lean_dec(v_a_4292_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4294_, lean_object* v_start_4295_, lean_object* v_lctx_4296_, lean_object* v_init_4297_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4295_, v_lctx_4296_, v_init_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4299_, lean_object* v_start_4300_, lean_object* v_lctx_4301_, lean_object* v_init_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4299_, v_start_4300_, v_lctx_4301_, v_init_4302_);
lean_dec(v_start_4300_);
return v_res_4303_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4304_, lean_object* v_a_4305_, lean_object* v_x_4306_){
_start:
{
uint8_t v___x_4307_; 
v___x_4307_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4305_, v_x_4306_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4308_, lean_object* v_a_4309_, lean_object* v_x_4310_){
_start:
{
uint8_t v_res_4311_; lean_object* v_r_4312_; 
v_res_4311_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4308_, v_a_4309_, v_x_4310_);
lean_dec(v_x_4310_);
lean_dec(v_a_4309_);
v_r_4312_ = lean_box(v_res_4311_);
return v_r_4312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4313_, lean_object* v_a_4314_, lean_object* v_x_4315_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4314_, v_x_4315_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4317_, lean_object* v_a_4318_, lean_object* v_x_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4317_, v_a_4318_, v_x_4319_);
lean_dec(v_a_4318_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4321_, lean_object* v_start_4322_, lean_object* v_t_4323_, lean_object* v_init_4324_){
_start:
{
lean_object* v___x_4325_; 
v___x_4325_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4322_, v_t_4323_, v_init_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4326_, lean_object* v_start_4327_, lean_object* v_t_4328_, lean_object* v_init_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4326_, v_start_4327_, v_t_4328_, v_init_4329_);
lean_dec(v_start_4327_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4331_, lean_object* v_start_4332_, lean_object* v_x_4333_, lean_object* v_x_4334_){
_start:
{
lean_object* v___x_4335_; 
v___x_4335_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4332_, v_x_4333_, v_x_4334_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4336_, lean_object* v_start_4337_, lean_object* v_x_4338_, lean_object* v_x_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4336_, v_start_4337_, v_x_4338_, v_x_4339_);
lean_dec(v_start_4337_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4341_, lean_object* v_start_4342_, lean_object* v_as_4343_, size_t v_i_4344_, size_t v_stop_4345_, lean_object* v_b_4346_){
_start:
{
lean_object* v___x_4347_; 
v___x_4347_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4342_, v_as_4343_, v_i_4344_, v_stop_4345_, v_b_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4348_, lean_object* v_start_4349_, lean_object* v_as_4350_, lean_object* v_i_4351_, lean_object* v_stop_4352_, lean_object* v_b_4353_){
_start:
{
size_t v_i_boxed_4354_; size_t v_stop_boxed_4355_; lean_object* v_res_4356_; 
v_i_boxed_4354_ = lean_unbox_usize(v_i_4351_);
lean_dec(v_i_4351_);
v_stop_boxed_4355_ = lean_unbox_usize(v_stop_4352_);
lean_dec(v_stop_4352_);
v_res_4356_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4348_, v_start_4349_, v_as_4350_, v_i_boxed_4354_, v_stop_boxed_4355_, v_b_4353_);
lean_dec_ref(v_as_4350_);
lean_dec(v_start_4349_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4357_, lean_object* v_start_4358_, lean_object* v_as_4359_, size_t v_i_4360_, size_t v_stop_4361_, lean_object* v_b_4362_){
_start:
{
lean_object* v___x_4363_; 
v___x_4363_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4358_, v_as_4359_, v_i_4360_, v_stop_4361_, v_b_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4364_, lean_object* v_start_4365_, lean_object* v_as_4366_, lean_object* v_i_4367_, lean_object* v_stop_4368_, lean_object* v_b_4369_){
_start:
{
size_t v_i_boxed_4370_; size_t v_stop_boxed_4371_; lean_object* v_res_4372_; 
v_i_boxed_4370_ = lean_unbox_usize(v_i_4367_);
lean_dec(v_i_4367_);
v_stop_boxed_4371_ = lean_unbox_usize(v_stop_4368_);
lean_dec(v_stop_4368_);
v_res_4372_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4364_, v_start_4365_, v_as_4366_, v_i_boxed_4370_, v_stop_boxed_4371_, v_b_4369_);
lean_dec_ref(v_as_4366_);
lean_dec(v_start_4365_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4373_, lean_object* v_inst_4374_){
_start:
{
lean_object* v___x_4375_; 
v___x_4375_ = lean_apply_2(v_inst_4373_, lean_box(0), v_inst_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4376_, lean_object* v_n_4377_, lean_object* v_inst_4378_, lean_object* v_inst_4379_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = lean_apply_2(v_inst_4378_, lean_box(0), v_inst_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4381_, lean_object* v_d_x3f_4382_, lean_object* v_b_4383_){
_start:
{
if (lean_obj_tag(v_d_x3f_4382_) == 0)
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4384_, 0, v_b_4383_);
v___x_4385_ = lean_apply_2(v_toPure_4381_, lean_box(0), v___x_4384_);
return v___x_4385_;
}
else
{
lean_object* v_val_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4401_; 
v_val_4386_ = lean_ctor_get(v_d_x3f_4382_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v_d_x3f_4382_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4388_ = v_d_x3f_4382_;
v_isShared_4389_ = v_isSharedCheck_4401_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_val_4386_);
lean_dec(v_d_x3f_4382_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4401_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
uint8_t v___x_4390_; 
v___x_4390_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4386_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4394_; 
v___x_4391_ = l_Lean_LocalDecl_toExpr(v_val_4386_);
v___x_4392_ = lean_array_push(v_b_4383_, v___x_4391_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v___x_4392_);
v___x_4394_ = v___x_4388_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4392_);
v___x_4394_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
lean_object* v___x_4395_; 
v___x_4395_ = lean_apply_2(v_toPure_4381_, lean_box(0), v___x_4394_);
return v___x_4395_;
}
}
else
{
lean_object* v___x_4398_; 
lean_dec(v_val_4386_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v_b_4383_);
v___x_4398_ = v___x_4388_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_b_4383_);
v___x_4398_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
lean_object* v___x_4399_; 
v___x_4399_ = lean_apply_2(v_toPure_4381_, lean_box(0), v___x_4398_);
return v___x_4399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4402_, lean_object* v_____s_4403_){
_start:
{
lean_object* v___x_4404_; 
v___x_4404_ = lean_apply_2(v_toPure_4402_, lean_box(0), v_____s_4403_);
return v___x_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4405_, lean_object* v_hs_4406_, lean_object* v___f_4407_, lean_object* v_toBind_4408_, lean_object* v___f_4409_, lean_object* v_____do__lift_4410_){
_start:
{
lean_object* v_decls_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v_decls_4411_ = lean_ctor_get(v_____do__lift_4410_, 1);
v___x_4412_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4405_, v_decls_4411_, v_hs_4406_, v___f_4407_);
v___x_4413_ = lean_apply_4(v_toBind_4408_, lean_box(0), lean_box(0), v___x_4412_, v___f_4409_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object* v_inst_4414_, lean_object* v_hs_4415_, lean_object* v___f_4416_, lean_object* v_toBind_4417_, lean_object* v___f_4418_, lean_object* v_____do__lift_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l_Lean_getLocalHyps___redArg___lam__2(v_inst_4414_, v_hs_4415_, v___f_4416_, v_toBind_4417_, v___f_4418_, v_____do__lift_4419_);
lean_dec_ref(v_____do__lift_4419_);
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4423_, lean_object* v_inst_4424_){
_start:
{
lean_object* v_toApplicative_4425_; lean_object* v_toBind_4426_; lean_object* v_toPure_4427_; lean_object* v_hs_4428_; lean_object* v___f_4429_; lean_object* v___f_4430_; lean_object* v___f_4431_; lean_object* v___x_4432_; 
v_toApplicative_4425_ = lean_ctor_get(v_inst_4423_, 0);
v_toBind_4426_ = lean_ctor_get(v_inst_4423_, 1);
lean_inc_n(v_toBind_4426_, 2);
v_toPure_4427_ = lean_ctor_get(v_toApplicative_4425_, 1);
v_hs_4428_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4427_, 2);
v___f_4429_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4429_, 0, v_toPure_4427_);
v___f_4430_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4430_, 0, v_toPure_4427_);
v___f_4431_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_4431_, 0, v_inst_4423_);
lean_closure_set(v___f_4431_, 1, v_hs_4428_);
lean_closure_set(v___f_4431_, 2, v___f_4429_);
lean_closure_set(v___f_4431_, 3, v_toBind_4426_);
lean_closure_set(v___f_4431_, 4, v___f_4430_);
v___x_4432_ = lean_apply_4(v_toBind_4426_, lean_box(0), lean_box(0), v_inst_4424_, v___f_4431_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4433_, lean_object* v_inst_4434_, lean_object* v_inst_4435_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = l_Lean_getLocalHyps___redArg(v_inst_4434_, v_inst_4435_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4437_, lean_object* v_e_4438_, lean_object* v_d_4439_){
_start:
{
lean_object* v___y_4441_; lean_object* v_fvarId_4473_; 
v_fvarId_4473_ = lean_ctor_get(v_d_4439_, 1);
lean_inc(v_fvarId_4473_);
v___y_4441_ = v_fvarId_4473_;
goto v___jp_4440_;
v___jp_4440_:
{
uint8_t v___x_4442_; 
v___x_4442_ = l_Lean_instBEqFVarId_beq(v___y_4441_, v_fvarId_4437_);
lean_dec(v___y_4441_);
if (v___x_4442_ == 0)
{
if (lean_obj_tag(v_d_4439_) == 0)
{
lean_object* v_index_4443_; lean_object* v_fvarId_4444_; lean_object* v_userName_4445_; lean_object* v_type_4446_; uint8_t v_bi_4447_; uint8_t v_kind_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4456_; 
v_index_4443_ = lean_ctor_get(v_d_4439_, 0);
v_fvarId_4444_ = lean_ctor_get(v_d_4439_, 1);
v_userName_4445_ = lean_ctor_get(v_d_4439_, 2);
v_type_4446_ = lean_ctor_get(v_d_4439_, 3);
v_bi_4447_ = lean_ctor_get_uint8(v_d_4439_, sizeof(void*)*4);
v_kind_4448_ = lean_ctor_get_uint8(v_d_4439_, sizeof(void*)*4 + 1);
v_isSharedCheck_4456_ = !lean_is_exclusive(v_d_4439_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4450_ = v_d_4439_;
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_type_4446_);
lean_inc(v_userName_4445_);
lean_inc(v_fvarId_4444_);
lean_inc(v_index_4443_);
lean_dec(v_d_4439_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4452_; lean_object* v___x_4454_; 
v___x_4452_ = l_Lean_Expr_replaceFVarId(v_type_4446_, v_fvarId_4437_, v_e_4438_);
lean_dec_ref(v_type_4446_);
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 3, v___x_4452_);
v___x_4454_ = v___x_4450_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_index_4443_);
lean_ctor_set(v_reuseFailAlloc_4455_, 1, v_fvarId_4444_);
lean_ctor_set(v_reuseFailAlloc_4455_, 2, v_userName_4445_);
lean_ctor_set(v_reuseFailAlloc_4455_, 3, v___x_4452_);
lean_ctor_set_uint8(v_reuseFailAlloc_4455_, sizeof(void*)*4, v_bi_4447_);
lean_ctor_set_uint8(v_reuseFailAlloc_4455_, sizeof(void*)*4 + 1, v_kind_4448_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
else
{
lean_object* v_index_4457_; lean_object* v_fvarId_4458_; lean_object* v_userName_4459_; lean_object* v_type_4460_; lean_object* v_value_4461_; uint8_t v_nondep_4462_; uint8_t v_kind_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4472_; 
v_index_4457_ = lean_ctor_get(v_d_4439_, 0);
v_fvarId_4458_ = lean_ctor_get(v_d_4439_, 1);
v_userName_4459_ = lean_ctor_get(v_d_4439_, 2);
v_type_4460_ = lean_ctor_get(v_d_4439_, 3);
v_value_4461_ = lean_ctor_get(v_d_4439_, 4);
v_nondep_4462_ = lean_ctor_get_uint8(v_d_4439_, sizeof(void*)*5);
v_kind_4463_ = lean_ctor_get_uint8(v_d_4439_, sizeof(void*)*5 + 1);
v_isSharedCheck_4472_ = !lean_is_exclusive(v_d_4439_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4465_ = v_d_4439_;
v_isShared_4466_ = v_isSharedCheck_4472_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_value_4461_);
lean_inc(v_type_4460_);
lean_inc(v_userName_4459_);
lean_inc(v_fvarId_4458_);
lean_inc(v_index_4457_);
lean_dec(v_d_4439_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4472_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4470_; 
lean_inc(v_fvarId_4437_);
v___x_4467_ = l_Lean_Expr_replaceFVarId(v_type_4460_, v_fvarId_4437_, v_e_4438_);
lean_dec_ref(v_type_4460_);
v___x_4468_ = l_Lean_Expr_replaceFVarId(v_value_4461_, v_fvarId_4437_, v_e_4438_);
lean_dec_ref(v_value_4461_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 4, v___x_4468_);
lean_ctor_set(v___x_4465_, 3, v___x_4467_);
v___x_4470_ = v___x_4465_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_index_4457_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_fvarId_4458_);
lean_ctor_set(v_reuseFailAlloc_4471_, 2, v_userName_4459_);
lean_ctor_set(v_reuseFailAlloc_4471_, 3, v___x_4467_);
lean_ctor_set(v_reuseFailAlloc_4471_, 4, v___x_4468_);
lean_ctor_set_uint8(v_reuseFailAlloc_4471_, sizeof(void*)*5, v_nondep_4462_);
lean_ctor_set_uint8(v_reuseFailAlloc_4471_, sizeof(void*)*5 + 1, v_kind_4463_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
else
{
lean_dec(v_fvarId_4437_);
return v_d_4439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4474_, lean_object* v_e_4475_, lean_object* v_d_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4474_, v_e_4475_, v_d_4476_);
lean_dec_ref(v_e_4475_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4478_, lean_object* v_e_4479_, lean_object* v_x_4480_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4478_, v_e_4479_, v_x_4480_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4482_, lean_object* v_e_4483_, lean_object* v_x_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4482_, v_e_4483_, v_x_4484_);
lean_dec_ref(v_e_4483_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4486_, lean_object* v_e_4487_, size_t v_sz_4488_, size_t v_i_4489_, lean_object* v_bs_4490_){
_start:
{
uint8_t v___x_4491_; 
v___x_4491_ = lean_usize_dec_lt(v_i_4489_, v_sz_4488_);
if (v___x_4491_ == 0)
{
lean_dec(v_fvarId_4486_);
return v_bs_4490_;
}
else
{
lean_object* v_v_4492_; lean_object* v___x_4493_; lean_object* v_bs_x27_4494_; lean_object* v___y_4496_; 
v_v_4492_ = lean_array_uget(v_bs_4490_, v_i_4489_);
v___x_4493_ = lean_unsigned_to_nat(0u);
v_bs_x27_4494_ = lean_array_uset(v_bs_4490_, v_i_4489_, v___x_4493_);
if (lean_obj_tag(v_v_4492_) == 0)
{
v___y_4496_ = v_v_4492_;
goto v___jp_4495_;
}
else
{
lean_object* v_val_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4509_; 
v_val_4501_ = lean_ctor_get(v_v_4492_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v_v_4492_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4503_ = v_v_4492_;
v_isShared_4504_ = v_isSharedCheck_4509_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_val_4501_);
lean_dec(v_v_4492_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4509_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4505_; lean_object* v___x_4507_; 
lean_inc(v_fvarId_4486_);
v___x_4505_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4486_, v_e_4487_, v_val_4501_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v___x_4505_);
v___x_4507_ = v___x_4503_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4505_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
v___y_4496_ = v___x_4507_;
goto v___jp_4495_;
}
}
}
v___jp_4495_:
{
size_t v___x_4497_; size_t v___x_4498_; lean_object* v___x_4499_; 
v___x_4497_ = ((size_t)1ULL);
v___x_4498_ = lean_usize_add(v_i_4489_, v___x_4497_);
v___x_4499_ = lean_array_uset(v_bs_x27_4494_, v_i_4489_, v___y_4496_);
v_i_4489_ = v___x_4498_;
v_bs_4490_ = v___x_4499_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4510_, lean_object* v_e_4511_, lean_object* v_sz_4512_, lean_object* v_i_4513_, lean_object* v_bs_4514_){
_start:
{
size_t v_sz_boxed_4515_; size_t v_i_boxed_4516_; lean_object* v_res_4517_; 
v_sz_boxed_4515_ = lean_unbox_usize(v_sz_4512_);
lean_dec(v_sz_4512_);
v_i_boxed_4516_ = lean_unbox_usize(v_i_4513_);
lean_dec(v_i_4513_);
v_res_4517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4510_, v_e_4511_, v_sz_boxed_4515_, v_i_boxed_4516_, v_bs_4514_);
lean_dec_ref(v_e_4511_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4518_, lean_object* v_e_4519_, size_t v_sz_4520_, size_t v_i_4521_, lean_object* v_bs_4522_){
_start:
{
uint8_t v___x_4523_; 
v___x_4523_ = lean_usize_dec_lt(v_i_4521_, v_sz_4520_);
if (v___x_4523_ == 0)
{
lean_dec(v_fvarId_4518_);
return v_bs_4522_;
}
else
{
lean_object* v_v_4524_; lean_object* v___x_4525_; lean_object* v_bs_x27_4526_; lean_object* v___x_4527_; size_t v___x_4528_; size_t v___x_4529_; lean_object* v___x_4530_; 
v_v_4524_ = lean_array_uget(v_bs_4522_, v_i_4521_);
v___x_4525_ = lean_unsigned_to_nat(0u);
v_bs_x27_4526_ = lean_array_uset(v_bs_4522_, v_i_4521_, v___x_4525_);
lean_inc(v_fvarId_4518_);
v___x_4527_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4518_, v_e_4519_, v_v_4524_);
v___x_4528_ = ((size_t)1ULL);
v___x_4529_ = lean_usize_add(v_i_4521_, v___x_4528_);
v___x_4530_ = lean_array_uset(v_bs_x27_4526_, v_i_4521_, v___x_4527_);
v_i_4521_ = v___x_4529_;
v_bs_4522_ = v___x_4530_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4532_, lean_object* v_e_4533_, lean_object* v_x_4534_){
_start:
{
if (lean_obj_tag(v_x_4534_) == 0)
{
lean_object* v_cs_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4545_; 
v_cs_4535_ = lean_ctor_get(v_x_4534_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_x_4534_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4537_ = v_x_4534_;
v_isShared_4538_ = v_isSharedCheck_4545_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_cs_4535_);
lean_dec(v_x_4534_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4545_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
size_t v_sz_4539_; size_t v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4543_; 
v_sz_4539_ = lean_array_size(v_cs_4535_);
v___x_4540_ = ((size_t)0ULL);
v___x_4541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4532_, v_e_4533_, v_sz_4539_, v___x_4540_, v_cs_4535_);
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 0, v___x_4541_);
v___x_4543_ = v___x_4537_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v___x_4541_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
else
{
lean_object* v_vs_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4556_; 
v_vs_4546_ = lean_ctor_get(v_x_4534_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v_x_4534_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4548_ = v_x_4534_;
v_isShared_4549_ = v_isSharedCheck_4556_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_vs_4546_);
lean_dec(v_x_4534_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4556_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
size_t v_sz_4550_; size_t v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4554_; 
v_sz_4550_ = lean_array_size(v_vs_4546_);
v___x_4551_ = ((size_t)0ULL);
v___x_4552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4532_, v_e_4533_, v_sz_4550_, v___x_4551_, v_vs_4546_);
if (v_isShared_4549_ == 0)
{
lean_ctor_set(v___x_4548_, 0, v___x_4552_);
v___x_4554_ = v___x_4548_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___x_4552_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4557_, lean_object* v_e_4558_, lean_object* v_x_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4557_, v_e_4558_, v_x_4559_);
lean_dec_ref(v_e_4558_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4561_, lean_object* v_e_4562_, lean_object* v_sz_4563_, lean_object* v_i_4564_, lean_object* v_bs_4565_){
_start:
{
size_t v_sz_boxed_4566_; size_t v_i_boxed_4567_; lean_object* v_res_4568_; 
v_sz_boxed_4566_ = lean_unbox_usize(v_sz_4563_);
lean_dec(v_sz_4563_);
v_i_boxed_4567_ = lean_unbox_usize(v_i_4564_);
lean_dec(v_i_4564_);
v_res_4568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4561_, v_e_4562_, v_sz_boxed_4566_, v_i_boxed_4567_, v_bs_4565_);
lean_dec_ref(v_e_4562_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4569_, lean_object* v_e_4570_, lean_object* v_t_4571_){
_start:
{
lean_object* v_root_4572_; lean_object* v_tail_4573_; lean_object* v_size_4574_; size_t v_shift_4575_; lean_object* v_tailOff_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4587_; 
v_root_4572_ = lean_ctor_get(v_t_4571_, 0);
v_tail_4573_ = lean_ctor_get(v_t_4571_, 1);
v_size_4574_ = lean_ctor_get(v_t_4571_, 2);
v_shift_4575_ = lean_ctor_get_usize(v_t_4571_, 4);
v_tailOff_4576_ = lean_ctor_get(v_t_4571_, 3);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_t_4571_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4578_ = v_t_4571_;
v_isShared_4579_ = v_isSharedCheck_4587_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_tailOff_4576_);
lean_inc(v_size_4574_);
lean_inc(v_tail_4573_);
lean_inc(v_root_4572_);
lean_dec(v_t_4571_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4587_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4580_; size_t v_sz_4581_; size_t v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4585_; 
lean_inc(v_fvarId_4569_);
v___x_4580_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4569_, v_e_4570_, v_root_4572_);
v_sz_4581_ = lean_array_size(v_tail_4573_);
v___x_4582_ = ((size_t)0ULL);
v___x_4583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4569_, v_e_4570_, v_sz_4581_, v___x_4582_, v_tail_4573_);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 1, v___x_4583_);
lean_ctor_set(v___x_4578_, 0, v___x_4580_);
v___x_4585_ = v___x_4578_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4586_, 1, v___x_4583_);
lean_ctor_set(v_reuseFailAlloc_4586_, 2, v_size_4574_);
lean_ctor_set(v_reuseFailAlloc_4586_, 3, v_tailOff_4576_);
lean_ctor_set_usize(v_reuseFailAlloc_4586_, 4, v_shift_4575_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4588_, lean_object* v_e_4589_, lean_object* v_t_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4588_, v_e_4589_, v_t_4590_);
lean_dec_ref(v_e_4589_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4592_, lean_object* v_x_4593_){
_start:
{
lean_object* v___x_4594_; 
v___x_4594_ = lean_apply_1(v_f_4592_, v_x_4593_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4595_, lean_object* v_as_4596_, lean_object* v_i_4597_, lean_object* v_acc_4598_){
_start:
{
lean_object* v___x_4599_; uint8_t v___x_4600_; 
v___x_4599_ = lean_array_get_size(v_as_4596_);
v___x_4600_ = lean_nat_dec_eq(v_i_4597_, v___x_4599_);
if (v___x_4600_ == 0)
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4601_ = lean_array_fget_borrowed(v_as_4596_, v_i_4597_);
lean_inc(v_f_4595_);
lean_inc(v___x_4601_);
v___x_4602_ = lean_apply_1(v_f_4595_, v___x_4601_);
v___x_4603_ = lean_unsigned_to_nat(1u);
v___x_4604_ = lean_nat_add(v_i_4597_, v___x_4603_);
lean_dec(v_i_4597_);
v___x_4605_ = lean_array_push(v_acc_4598_, v___x_4602_);
v_i_4597_ = v___x_4604_;
v_acc_4598_ = v___x_4605_;
goto _start;
}
else
{
lean_dec(v_i_4597_);
lean_dec(v_f_4595_);
return v_acc_4598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4607_, lean_object* v_as_4608_, lean_object* v_i_4609_, lean_object* v_acc_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4607_, v_as_4608_, v_i_4609_, v_acc_4610_);
lean_dec_ref(v_as_4608_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4612_, lean_object* v_as_4613_){
_start:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4614_ = lean_unsigned_to_nat(0u);
v___x_4615_ = lean_array_get_size(v_as_4613_);
v___x_4616_ = lean_mk_empty_array_with_capacity(v___x_4615_);
v___x_4617_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4612_, v_as_4613_, v___x_4614_, v___x_4616_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4618_, lean_object* v_as_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4618_, v_as_4619_);
lean_dec_ref(v_as_4619_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4621_, size_t v_sz_4622_, size_t v_i_4623_, lean_object* v_bs_4624_){
_start:
{
uint8_t v___x_4625_; 
v___x_4625_ = lean_usize_dec_lt(v_i_4623_, v_sz_4622_);
if (v___x_4625_ == 0)
{
lean_dec(v_f_4621_);
return v_bs_4624_;
}
else
{
lean_object* v_v_4626_; lean_object* v___x_4627_; lean_object* v_bs_x27_4628_; lean_object* v___y_4630_; 
v_v_4626_ = lean_array_uget(v_bs_4624_, v_i_4623_);
v___x_4627_ = lean_unsigned_to_nat(0u);
v_bs_x27_4628_ = lean_array_uset(v_bs_4624_, v_i_4623_, v___x_4627_);
switch(lean_obj_tag(v_v_4626_))
{
case 0:
{
lean_object* v_key_4635_; lean_object* v_val_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4644_; 
v_key_4635_ = lean_ctor_get(v_v_4626_, 0);
v_val_4636_ = lean_ctor_get(v_v_4626_, 1);
v_isSharedCheck_4644_ = !lean_is_exclusive(v_v_4626_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4638_ = v_v_4626_;
v_isShared_4639_ = v_isSharedCheck_4644_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_val_4636_);
lean_inc(v_key_4635_);
lean_dec(v_v_4626_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4644_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4640_; lean_object* v___x_4642_; 
lean_inc(v_f_4621_);
v___x_4640_ = lean_apply_1(v_f_4621_, v_val_4636_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 1, v___x_4640_);
v___x_4642_ = v___x_4638_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_key_4635_);
lean_ctor_set(v_reuseFailAlloc_4643_, 1, v___x_4640_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
v___y_4630_ = v___x_4642_;
goto v___jp_4629_;
}
}
}
case 1:
{
lean_object* v_node_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4653_; 
v_node_4645_ = lean_ctor_get(v_v_4626_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v_v_4626_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4647_ = v_v_4626_;
v_isShared_4648_ = v_isSharedCheck_4653_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_node_4645_);
lean_dec(v_v_4626_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4653_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4649_; lean_object* v___x_4651_; 
lean_inc(v_f_4621_);
v___x_4649_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4621_, v_node_4645_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 0, v___x_4649_);
v___x_4651_ = v___x_4647_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4649_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
v___y_4630_ = v___x_4651_;
goto v___jp_4629_;
}
}
}
default: 
{
lean_object* v___x_4654_; 
v___x_4654_ = lean_box(2);
v___y_4630_ = v___x_4654_;
goto v___jp_4629_;
}
}
v___jp_4629_:
{
size_t v___x_4631_; size_t v___x_4632_; lean_object* v___x_4633_; 
v___x_4631_ = ((size_t)1ULL);
v___x_4632_ = lean_usize_add(v_i_4623_, v___x_4631_);
v___x_4633_ = lean_array_uset(v_bs_x27_4628_, v_i_4623_, v___y_4630_);
v_i_4623_ = v___x_4632_;
v_bs_4624_ = v___x_4633_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4655_, lean_object* v_n_4656_){
_start:
{
if (lean_obj_tag(v_n_4656_) == 0)
{
lean_object* v_es_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4667_; 
v_es_4657_ = lean_ctor_get(v_n_4656_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v_n_4656_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4659_ = v_n_4656_;
v_isShared_4660_ = v_isSharedCheck_4667_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_es_4657_);
lean_dec(v_n_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4667_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
size_t v_sz_4661_; size_t v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4665_; 
v_sz_4661_ = lean_array_size(v_es_4657_);
v___x_4662_ = ((size_t)0ULL);
v___x_4663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4655_, v_sz_4661_, v___x_4662_, v_es_4657_);
if (v_isShared_4660_ == 0)
{
lean_ctor_set(v___x_4659_, 0, v___x_4663_);
v___x_4665_ = v___x_4659_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4663_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
else
{
lean_object* v_ks_4668_; lean_object* v_vs_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4677_; 
v_ks_4668_ = lean_ctor_get(v_n_4656_, 0);
v_vs_4669_ = lean_ctor_get(v_n_4656_, 1);
v_isSharedCheck_4677_ = !lean_is_exclusive(v_n_4656_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4671_ = v_n_4656_;
v_isShared_4672_ = v_isSharedCheck_4677_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_vs_4669_);
lean_inc(v_ks_4668_);
lean_dec(v_n_4656_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4677_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v_val_4673_; lean_object* v___x_4675_; 
v_val_4673_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4655_, v_vs_4669_);
lean_dec_ref(v_vs_4669_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 1, v_val_4673_);
v___x_4675_ = v___x_4671_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_ks_4668_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_val_4673_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4678_, lean_object* v_sz_4679_, lean_object* v_i_4680_, lean_object* v_bs_4681_){
_start:
{
size_t v_sz_boxed_4682_; size_t v_i_boxed_4683_; lean_object* v_res_4684_; 
v_sz_boxed_4682_ = lean_unbox_usize(v_sz_4679_);
lean_dec(v_sz_4679_);
v_i_boxed_4683_ = lean_unbox_usize(v_i_4680_);
lean_dec(v_i_4680_);
v_res_4684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4678_, v_sz_boxed_4682_, v_i_boxed_4683_, v_bs_4681_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4685_, lean_object* v_f_4686_){
_start:
{
lean_object* v___f_4687_; lean_object* v___x_4688_; 
v___f_4687_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4687_, 0, v_f_4686_);
v___x_4688_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4687_, v_pm_4685_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4689_, lean_object* v_e_4690_, lean_object* v_lctx_4691_){
_start:
{
lean_object* v_lctx_4692_; lean_object* v_fvarIdToDecl_4693_; lean_object* v_decls_4694_; lean_object* v_auxDeclToFullName_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4705_; 
lean_inc(v_fvarId_4689_);
v_lctx_4692_ = lean_local_ctx_erase(v_lctx_4691_, v_fvarId_4689_);
v_fvarIdToDecl_4693_ = lean_ctor_get(v_lctx_4692_, 0);
v_decls_4694_ = lean_ctor_get(v_lctx_4692_, 1);
v_auxDeclToFullName_4695_ = lean_ctor_get(v_lctx_4692_, 2);
v_isSharedCheck_4705_ = !lean_is_exclusive(v_lctx_4692_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4697_ = v_lctx_4692_;
v_isShared_4698_ = v_isSharedCheck_4705_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_auxDeclToFullName_4695_);
lean_inc(v_decls_4694_);
lean_inc(v_fvarIdToDecl_4693_);
lean_dec(v_lctx_4692_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4705_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___f_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4703_; 
lean_inc_ref(v_e_4690_);
lean_inc(v_fvarId_4689_);
v___f_4699_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4699_, 0, v_fvarId_4689_);
lean_closure_set(v___f_4699_, 1, v_e_4690_);
v___x_4700_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4693_, v___f_4699_);
v___x_4701_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4689_, v_e_4690_, v_decls_4694_);
lean_dec_ref(v_e_4690_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 1, v___x_4701_);
lean_ctor_set(v___x_4697_, 0, v___x_4700_);
v___x_4703_ = v___x_4697_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4700_);
lean_ctor_set(v_reuseFailAlloc_4704_, 1, v___x_4701_);
lean_ctor_set(v_reuseFailAlloc_4704_, 2, v_auxDeclToFullName_4695_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4706_, lean_object* v_00_u03c3_4707_, lean_object* v_pm_4708_, lean_object* v_f_4709_){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4708_, v_f_4709_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4711_, lean_object* v_f_4712_){
_start:
{
lean_object* v___x_4713_; 
v___x_4713_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4712_, v_pm_4711_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4714_, lean_object* v_00_u03c3_4715_, lean_object* v_pm_4716_, lean_object* v_f_4717_){
_start:
{
lean_object* v___x_4718_; 
v___x_4718_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4717_, v_pm_4716_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4719_, lean_object* v_00_u03b2_4720_, lean_object* v_00_u03c3_4721_, lean_object* v_f_4722_, lean_object* v_n_4723_){
_start:
{
lean_object* v___x_4724_; 
v___x_4724_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4722_, v_n_4723_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4725_, lean_object* v_00_u03b2_4726_, lean_object* v_00_u03c3_4727_, lean_object* v_f_4728_, size_t v_sz_4729_, size_t v_i_4730_, lean_object* v_bs_4731_){
_start:
{
lean_object* v___x_4732_; 
v___x_4732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4728_, v_sz_4729_, v_i_4730_, v_bs_4731_);
return v___x_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4733_, lean_object* v_00_u03b2_4734_, lean_object* v_00_u03c3_4735_, lean_object* v_f_4736_, lean_object* v_sz_4737_, lean_object* v_i_4738_, lean_object* v_bs_4739_){
_start:
{
size_t v_sz_boxed_4740_; size_t v_i_boxed_4741_; lean_object* v_res_4742_; 
v_sz_boxed_4740_ = lean_unbox_usize(v_sz_4737_);
lean_dec(v_sz_4737_);
v_i_boxed_4741_ = lean_unbox_usize(v_i_4738_);
lean_dec(v_i_4738_);
v_res_4742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4733_, v_00_u03b2_4734_, v_00_u03c3_4735_, v_f_4736_, v_sz_boxed_4740_, v_i_boxed_4741_, v_bs_4739_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4743_, lean_object* v_00_u03b2_4744_, lean_object* v_f_4745_, lean_object* v_as_4746_){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4745_, v_as_4746_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4748_, lean_object* v_00_u03b2_4749_, lean_object* v_f_4750_, lean_object* v_as_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4748_, v_00_u03b2_4749_, v_f_4750_, v_as_4751_);
lean_dec_ref(v_as_4751_);
return v_res_4752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4753_, lean_object* v_00_u03b2_4754_, lean_object* v_f_4755_, lean_object* v_as_4756_, lean_object* v_i_4757_, lean_object* v_acc_4758_, lean_object* v_hle_4759_){
_start:
{
lean_object* v___x_4760_; 
v___x_4760_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4755_, v_as_4756_, v_i_4757_, v_acc_4758_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4761_, lean_object* v_00_u03b2_4762_, lean_object* v_f_4763_, lean_object* v_as_4764_, lean_object* v_i_4765_, lean_object* v_acc_4766_, lean_object* v_hle_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4761_, v_00_u03b2_4762_, v_f_4763_, v_as_4764_, v_i_4765_, v_acc_4766_, v_hle_4767_);
lean_dec_ref(v_as_4764_);
return v_res_4768_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Control(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLocalDeclKind_default = _init_l_Lean_instInhabitedLocalDeclKind_default();
l_Lean_instInhabitedLocalDeclKind = _init_l_Lean_instInhabitedLocalDeclKind();
l_Lean_instInhabitedLocalDecl_default = _init_l_Lean_instInhabitedLocalDecl_default();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl_default);
l_Lean_instInhabitedLocalDecl = _init_l_Lean_instInhabitedLocalDecl();
lean_mark_persistent(l_Lean_instInhabitedLocalDecl);
l_Lean_instInhabitedLocalContext_default = _init_l_Lean_instInhabitedLocalContext_default();
lean_mark_persistent(l_Lean_instInhabitedLocalContext_default);
l_Lean_instInhabitedLocalContext = _init_l_Lean_instInhabitedLocalContext();
lean_mark_persistent(l_Lean_instInhabitedLocalContext);
l_Lean_LocalContext_empty = _init_l_Lean_LocalContext_empty();
lean_mark_persistent(l_Lean_LocalContext_empty);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Control(uint8_t builtin);
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LocalContext(builtin);
}
#ifdef __cplusplus
}
#endif
