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
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object* v_lctx_2765_, lean_object* v_fvarId_2766_, lean_object* v_type_2767_){
_start:
{
lean_object* v_fvarIdToDecl_2768_; lean_object* v_decls_2769_; lean_object* v_auxDeclToFullName_2770_; lean_object* v___x_2771_; 
v_fvarIdToDecl_2768_ = lean_ctor_get(v_lctx_2765_, 0);
v_decls_2769_ = lean_ctor_get(v_lctx_2765_, 1);
v_auxDeclToFullName_2770_ = lean_ctor_get(v_lctx_2765_, 2);
lean_inc_ref(v_lctx_2765_);
v___x_2771_ = lean_local_ctx_find(v_lctx_2765_, v_fvarId_2766_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_dec_ref(v_type_2767_);
return v_lctx_2765_;
}
else
{
lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2796_; 
lean_inc(v_auxDeclToFullName_2770_);
lean_inc_ref(v_decls_2769_);
lean_inc_ref(v_fvarIdToDecl_2768_);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_lctx_2765_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; lean_object* v_unused_2798_; lean_object* v_unused_2799_; 
v_unused_2797_ = lean_ctor_get(v_lctx_2765_, 2);
lean_dec(v_unused_2797_);
v_unused_2798_ = lean_ctor_get(v_lctx_2765_, 1);
lean_dec(v_unused_2798_);
v_unused_2799_ = lean_ctor_get(v_lctx_2765_, 0);
lean_dec(v_unused_2799_);
v___x_2773_ = v_lctx_2765_;
v_isShared_2774_ = v_isSharedCheck_2796_;
goto v_resetjp_2772_;
}
else
{
lean_dec(v_lctx_2765_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2796_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v_val_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2795_; 
v_val_2775_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2777_ = v___x_2771_;
v_isShared_2778_ = v_isSharedCheck_2795_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_val_2775_);
lean_dec(v___x_2771_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2795_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v_decl_2779_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2791_; lean_object* v_fvarId_2794_; 
v_decl_2779_ = l_Lean_LocalDecl_setType(v_val_2775_, v_type_2767_);
v_fvarId_2794_ = lean_ctor_get(v_decl_2779_, 1);
lean_inc(v_fvarId_2794_);
v___y_2791_ = v_fvarId_2794_;
goto v___jp_2790_;
v___jp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v_decl_2779_);
v___x_2784_ = v___x_2777_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_decl_2779_);
v___x_2784_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = l_Lean_PersistentArray_set___redArg(v_decls_2769_, v___y_2782_, v___x_2784_);
lean_dec(v___y_2782_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2785_);
lean_ctor_set(v___x_2773_, 0, v___y_2781_);
v___x_2787_ = v___x_2773_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___y_2781_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_auxDeclToFullName_2770_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
v___jp_2790_:
{
lean_object* v___x_2792_; lean_object* v_index_2793_; 
lean_inc_ref(v_decl_2779_);
v___x_2792_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2768_, v___y_2791_, v_decl_2779_);
v_index_2793_ = lean_ctor_get(v_decl_2779_, 0);
lean_inc(v_index_2793_);
v___y_2781_ = v___x_2792_;
v___y_2782_ = v_index_2793_;
goto v___jp_2780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2800_){
_start:
{
lean_object* v_decls_2801_; lean_object* v_size_2802_; 
v_decls_2801_ = lean_ctor_get(v_lctx_2800_, 1);
lean_inc_ref(v_decls_2801_);
lean_dec_ref(v_lctx_2800_);
v_size_2802_ = lean_ctor_get(v_decls_2801_, 2);
lean_inc(v_size_2802_);
lean_dec_ref(v_decls_2801_);
return v_size_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2803_, lean_object* v_i_2804_){
_start:
{
lean_object* v_decls_2805_; lean_object* v_size_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; 
v_decls_2805_ = lean_ctor_get(v_lctx_2803_, 1);
v_size_2806_ = lean_ctor_get(v_decls_2805_, 2);
v___x_2807_ = lean_box(0);
v___x_2808_ = lean_nat_dec_lt(v_i_2804_, v_size_2806_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; 
v___x_2809_ = l_outOfBounds___redArg(v___x_2807_);
return v___x_2809_;
}
else
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2807_, v_decls_2805_, v_i_2804_);
return v___x_2810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2811_, lean_object* v_i_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2811_, v_i_2812_);
lean_dec(v_i_2812_);
lean_dec_ref(v_lctx_2811_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2814_, lean_object* v_f_2815_, lean_object* v_b_2816_, lean_object* v_decl_2817_){
_start:
{
if (lean_obj_tag(v_decl_2817_) == 0)
{
lean_object* v___x_2818_; 
lean_dec(v_f_2815_);
v___x_2818_ = lean_apply_2(v_toPure_2814_, lean_box(0), v_b_2816_);
return v___x_2818_;
}
else
{
lean_object* v_val_2819_; lean_object* v___x_2820_; 
lean_dec(v_toPure_2814_);
v_val_2819_ = lean_ctor_get(v_decl_2817_, 0);
lean_inc(v_val_2819_);
lean_dec_ref(v_decl_2817_);
v___x_2820_ = lean_apply_2(v_f_2815_, v_b_2816_, v_val_2819_);
return v___x_2820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2821_, lean_object* v_lctx_2822_, lean_object* v_f_2823_, lean_object* v_init_2824_, lean_object* v_start_2825_){
_start:
{
lean_object* v_toApplicative_2826_; lean_object* v_decls_2827_; lean_object* v_toPure_2828_; lean_object* v___f_2829_; lean_object* v___x_2830_; 
v_toApplicative_2826_ = lean_ctor_get(v_inst_2821_, 0);
v_decls_2827_ = lean_ctor_get(v_lctx_2822_, 1);
lean_inc_ref(v_decls_2827_);
lean_dec_ref(v_lctx_2822_);
v_toPure_2828_ = lean_ctor_get(v_toApplicative_2826_, 1);
lean_inc(v_toPure_2828_);
v___f_2829_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2829_, 0, v_toPure_2828_);
lean_closure_set(v___f_2829_, 1, v_f_2823_);
v___x_2830_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2821_, v_decls_2827_, v___f_2829_, v_init_2824_, v_start_2825_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2831_, lean_object* v_lctx_2832_, lean_object* v_f_2833_, lean_object* v_init_2834_, lean_object* v_start_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2831_, v_lctx_2832_, v_f_2833_, v_init_2834_, v_start_2835_);
lean_dec(v_start_2835_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2837_, lean_object* v_00_u03b2_2838_, lean_object* v_inst_2839_, lean_object* v_lctx_2840_, lean_object* v_f_2841_, lean_object* v_init_2842_, lean_object* v_start_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2839_, v_lctx_2840_, v_f_2841_, v_init_2842_, v_start_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2845_, lean_object* v_00_u03b2_2846_, lean_object* v_inst_2847_, lean_object* v_lctx_2848_, lean_object* v_f_2849_, lean_object* v_init_2850_, lean_object* v_start_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_LocalContext_foldlM(v_m_2845_, v_00_u03b2_2846_, v_inst_2847_, v_lctx_2848_, v_f_2849_, v_init_2850_, v_start_2851_);
lean_dec(v_start_2851_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2853_, lean_object* v_f_2854_, lean_object* v_decl_2855_, lean_object* v_b_2856_){
_start:
{
if (lean_obj_tag(v_decl_2855_) == 0)
{
lean_object* v___x_2857_; 
lean_dec(v_f_2854_);
v___x_2857_ = lean_apply_2(v_toPure_2853_, lean_box(0), v_b_2856_);
return v___x_2857_;
}
else
{
lean_object* v_val_2858_; lean_object* v___x_2859_; 
lean_dec(v_toPure_2853_);
v_val_2858_ = lean_ctor_get(v_decl_2855_, 0);
lean_inc(v_val_2858_);
lean_dec_ref(v_decl_2855_);
v___x_2859_ = lean_apply_2(v_f_2854_, v_val_2858_, v_b_2856_);
return v___x_2859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2860_, lean_object* v_lctx_2861_, lean_object* v_f_2862_, lean_object* v_init_2863_){
_start:
{
lean_object* v_toApplicative_2864_; lean_object* v_decls_2865_; lean_object* v_toPure_2866_; lean_object* v___f_2867_; lean_object* v___x_2868_; 
v_toApplicative_2864_ = lean_ctor_get(v_inst_2860_, 0);
v_decls_2865_ = lean_ctor_get(v_lctx_2861_, 1);
lean_inc_ref(v_decls_2865_);
lean_dec_ref(v_lctx_2861_);
v_toPure_2866_ = lean_ctor_get(v_toApplicative_2864_, 1);
lean_inc(v_toPure_2866_);
v___f_2867_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2867_, 0, v_toPure_2866_);
lean_closure_set(v___f_2867_, 1, v_f_2862_);
v___x_2868_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2860_, v_decls_2865_, v___f_2867_, v_init_2863_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2869_, lean_object* v_00_u03b2_2870_, lean_object* v_inst_2871_, lean_object* v_lctx_2872_, lean_object* v_f_2873_, lean_object* v_init_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2871_, v_lctx_2872_, v_f_2873_, v_init_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2876_, lean_object* v_f_2877_, lean_object* v_decl_2878_){
_start:
{
if (lean_obj_tag(v_decl_2878_) == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
lean_dec(v_f_2877_);
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_apply_2(v_toPure_2876_, lean_box(0), v___x_2879_);
return v___x_2880_;
}
else
{
lean_object* v_val_2881_; lean_object* v___x_2882_; 
lean_dec(v_toPure_2876_);
v_val_2881_ = lean_ctor_get(v_decl_2878_, 0);
lean_inc(v_val_2881_);
lean_dec_ref(v_decl_2878_);
v___x_2882_ = lean_apply_1(v_f_2877_, v_val_2881_);
return v___x_2882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2883_, lean_object* v_lctx_2884_, lean_object* v_f_2885_, lean_object* v_start_2886_){
_start:
{
lean_object* v_toApplicative_2887_; lean_object* v_decls_2888_; lean_object* v_toPure_2889_; lean_object* v___f_2890_; lean_object* v___x_2891_; 
v_toApplicative_2887_ = lean_ctor_get(v_inst_2883_, 0);
v_decls_2888_ = lean_ctor_get(v_lctx_2884_, 1);
lean_inc_ref(v_decls_2888_);
lean_dec_ref(v_lctx_2884_);
v_toPure_2889_ = lean_ctor_get(v_toApplicative_2887_, 1);
lean_inc(v_toPure_2889_);
v___f_2890_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2890_, 0, v_toPure_2889_);
lean_closure_set(v___f_2890_, 1, v_f_2885_);
v___x_2891_ = l_Lean_PersistentArray_forM___redArg(v_inst_2883_, v_decls_2888_, v___f_2890_, v_start_2886_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2892_, lean_object* v_lctx_2893_, lean_object* v_f_2894_, lean_object* v_start_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lean_LocalContext_forM___redArg(v_inst_2892_, v_lctx_2893_, v_f_2894_, v_start_2895_);
lean_dec(v_start_2895_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2897_, lean_object* v_inst_2898_, lean_object* v_lctx_2899_, lean_object* v_f_2900_, lean_object* v_start_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_LocalContext_forM___redArg(v_inst_2898_, v_lctx_2899_, v_f_2900_, v_start_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2903_, lean_object* v_inst_2904_, lean_object* v_lctx_2905_, lean_object* v_f_2906_, lean_object* v_start_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_LocalContext_forM(v_m_2903_, v_inst_2904_, v_lctx_2905_, v_f_2906_, v_start_2907_);
lean_dec(v_start_2907_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2909_, lean_object* v_f_2910_, lean_object* v_decl_2911_){
_start:
{
if (lean_obj_tag(v_decl_2911_) == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_dec(v_f_2910_);
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_apply_2(v_toPure_2909_, lean_box(0), v___x_2912_);
return v___x_2913_;
}
else
{
lean_object* v_val_2914_; lean_object* v___x_2915_; 
lean_dec(v_toPure_2909_);
v_val_2914_ = lean_ctor_get(v_decl_2911_, 0);
lean_inc(v_val_2914_);
lean_dec_ref(v_decl_2911_);
v___x_2915_ = lean_apply_1(v_f_2910_, v_val_2914_);
return v___x_2915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2916_, lean_object* v_lctx_2917_, lean_object* v_f_2918_){
_start:
{
lean_object* v_toApplicative_2919_; lean_object* v_decls_2920_; lean_object* v_toPure_2921_; lean_object* v___f_2922_; lean_object* v___x_2923_; 
v_toApplicative_2919_ = lean_ctor_get(v_inst_2916_, 0);
v_decls_2920_ = lean_ctor_get(v_lctx_2917_, 1);
lean_inc_ref(v_decls_2920_);
lean_dec_ref(v_lctx_2917_);
v_toPure_2921_ = lean_ctor_get(v_toApplicative_2919_, 1);
lean_inc(v_toPure_2921_);
v___f_2922_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2922_, 0, v_toPure_2921_);
lean_closure_set(v___f_2922_, 1, v_f_2918_);
v___x_2923_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2916_, v_decls_2920_, v___f_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2924_, lean_object* v_00_u03b2_2925_, lean_object* v_inst_2926_, lean_object* v_lctx_2927_, lean_object* v_f_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2926_, v_lctx_2927_, v_f_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2930_, lean_object* v_lctx_2931_, lean_object* v_f_2932_){
_start:
{
lean_object* v_toApplicative_2933_; lean_object* v_decls_2934_; lean_object* v_toPure_2935_; lean_object* v___f_2936_; lean_object* v___x_2937_; 
v_toApplicative_2933_ = lean_ctor_get(v_inst_2930_, 0);
v_decls_2934_ = lean_ctor_get(v_lctx_2931_, 1);
lean_inc_ref(v_decls_2934_);
lean_dec_ref(v_lctx_2931_);
v_toPure_2935_ = lean_ctor_get(v_toApplicative_2933_, 1);
lean_inc(v_toPure_2935_);
v___f_2936_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2936_, 0, v_toPure_2935_);
lean_closure_set(v___f_2936_, 1, v_f_2932_);
v___x_2937_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2930_, v_decls_2934_, v___f_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2938_, lean_object* v_00_u03b2_2939_, lean_object* v_inst_2940_, lean_object* v_lctx_2941_, lean_object* v_f_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2940_, v_lctx_2941_, v_f_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2944_, lean_object* v_f_2945_, lean_object* v_d_x3f_2946_, lean_object* v_b_2947_){
_start:
{
if (lean_obj_tag(v_d_x3f_2946_) == 0)
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
lean_dec(v_f_2945_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_b_2947_);
v___x_2949_ = lean_apply_2(v_toPure_2944_, lean_box(0), v___x_2948_);
return v___x_2949_;
}
else
{
lean_object* v_val_2950_; lean_object* v___x_2951_; 
lean_dec(v_toPure_2944_);
v_val_2950_ = lean_ctor_get(v_d_x3f_2946_, 0);
lean_inc(v_val_2950_);
lean_dec_ref(v_d_x3f_2946_);
v___x_2951_ = lean_apply_2(v_f_2945_, v_val_2950_, v_b_2947_);
return v___x_2951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2952_, lean_object* v_inst_2953_, lean_object* v_00_u03b2_2954_, lean_object* v_lctx_2955_, lean_object* v_init_2956_, lean_object* v_f_2957_){
_start:
{
lean_object* v_decls_2958_; lean_object* v___f_2959_; lean_object* v___x_2960_; 
v_decls_2958_ = lean_ctor_get(v_lctx_2955_, 1);
v___f_2959_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2959_, 0, v_toPure_2952_);
lean_closure_set(v___f_2959_, 1, v_f_2957_);
v___x_2960_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2953_, v_decls_2958_, v_init_2956_, v___f_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object* v_toPure_2961_, lean_object* v_inst_2962_, lean_object* v_00_u03b2_2963_, lean_object* v_lctx_2964_, lean_object* v_init_2965_, lean_object* v_f_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(v_toPure_2961_, v_inst_2962_, v_00_u03b2_2963_, v_lctx_2964_, v_init_2965_, v_f_2966_);
lean_dec_ref(v_lctx_2964_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2968_){
_start:
{
lean_object* v_toApplicative_2969_; lean_object* v_toPure_2970_; lean_object* v___f_2971_; 
v_toApplicative_2969_ = lean_ctor_get(v_inst_2968_, 0);
v_toPure_2970_ = lean_ctor_get(v_toApplicative_2969_, 1);
lean_inc(v_toPure_2970_);
v___f_2971_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2971_, 0, v_toPure_2970_);
lean_closure_set(v___f_2971_, 1, v_inst_2968_);
return v___f_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2972_, lean_object* v_inst_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2975_, lean_object* v_x1_2976_, lean_object* v_x2_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_apply_2(v_f_2975_, v_x1_2976_, v_x2_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2998_, lean_object* v_f_2999_, lean_object* v_init_3000_, lean_object* v_start_3001_){
_start:
{
lean_object* v___f_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___f_3002_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3002_, 0, v_f_2999_);
v___x_3003_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3004_ = l_Lean_LocalContext_foldlM___redArg(v___x_3003_, v_lctx_2998_, v___f_3002_, v_init_3000_, v_start_3001_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_3005_, lean_object* v_f_3006_, lean_object* v_init_3007_, lean_object* v_start_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_LocalContext_foldl___redArg(v_lctx_3005_, v_f_3006_, v_init_3007_, v_start_3008_);
lean_dec(v_start_3008_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_3010_, lean_object* v_lctx_3011_, lean_object* v_f_3012_, lean_object* v_init_3013_, lean_object* v_start_3014_){
_start:
{
lean_object* v___f_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___f_3015_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3015_, 0, v_f_3012_);
v___x_3016_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3017_ = l_Lean_LocalContext_foldlM___redArg(v___x_3016_, v_lctx_3011_, v___f_3015_, v_init_3013_, v_start_3014_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_3018_, lean_object* v_lctx_3019_, lean_object* v_f_3020_, lean_object* v_init_3021_, lean_object* v_start_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_LocalContext_foldl(v_00_u03b2_3018_, v_lctx_3019_, v_f_3020_, v_init_3021_, v_start_3022_);
lean_dec(v_start_3022_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_3024_, lean_object* v_x1_3025_, lean_object* v_x2_3026_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_apply_2(v_f_3024_, v_x1_3025_, v_x2_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_3028_, lean_object* v_f_3029_, lean_object* v_init_3030_){
_start:
{
lean_object* v___f_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___f_3031_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3031_, 0, v_f_3029_);
v___x_3032_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3033_ = l_Lean_LocalContext_foldrM___redArg(v___x_3032_, v_lctx_3028_, v___f_3031_, v_init_3030_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_3034_, lean_object* v_lctx_3035_, lean_object* v_f_3036_, lean_object* v_init_3037_){
_start:
{
lean_object* v___f_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___f_3038_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3038_, 0, v_f_3036_);
v___x_3039_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3040_ = l_Lean_LocalContext_foldrM___redArg(v___x_3039_, v_lctx_3035_, v___f_3038_, v_init_3037_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_3041_, size_t v_i_3042_, size_t v_stop_3043_, lean_object* v_b_3044_){
_start:
{
lean_object* v___y_3046_; uint8_t v___x_3050_; 
v___x_3050_ = lean_usize_dec_eq(v_i_3042_, v_stop_3043_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; 
v___x_3051_ = lean_array_uget_borrowed(v_as_3041_, v_i_3042_);
if (lean_obj_tag(v___x_3051_) == 0)
{
v___y_3046_ = v_b_3044_;
goto v___jp_3045_;
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_unsigned_to_nat(1u);
v___x_3053_ = lean_nat_add(v_b_3044_, v___x_3052_);
lean_dec(v_b_3044_);
v___y_3046_ = v___x_3053_;
goto v___jp_3045_;
}
}
else
{
return v_b_3044_;
}
v___jp_3045_:
{
size_t v___x_3047_; size_t v___x_3048_; 
v___x_3047_ = ((size_t)1ULL);
v___x_3048_ = lean_usize_add(v_i_3042_, v___x_3047_);
v_i_3042_ = v___x_3048_;
v_b_3044_ = v___y_3046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3054_, lean_object* v_i_3055_, lean_object* v_stop_3056_, lean_object* v_b_3057_){
_start:
{
size_t v_i_boxed_3058_; size_t v_stop_boxed_3059_; lean_object* v_res_3060_; 
v_i_boxed_3058_ = lean_unbox_usize(v_i_3055_);
lean_dec(v_i_3055_);
v_stop_boxed_3059_ = lean_unbox_usize(v_stop_3056_);
lean_dec(v_stop_3056_);
v_res_3060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_3054_, v_i_boxed_3058_, v_stop_boxed_3059_, v_b_3057_);
lean_dec_ref(v_as_3054_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3061_, lean_object* v_x_3062_){
_start:
{
if (lean_obj_tag(v_x_3061_) == 0)
{
lean_object* v_cs_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v_cs_3063_ = lean_ctor_get(v_x_3061_, 0);
v___x_3064_ = lean_unsigned_to_nat(0u);
v___x_3065_ = lean_array_get_size(v_cs_3063_);
v___x_3066_ = lean_nat_dec_lt(v___x_3064_, v___x_3065_);
if (v___x_3066_ == 0)
{
return v_x_3062_;
}
else
{
uint8_t v___x_3067_; 
v___x_3067_ = lean_nat_dec_le(v___x_3065_, v___x_3065_);
if (v___x_3067_ == 0)
{
if (v___x_3066_ == 0)
{
return v_x_3062_;
}
else
{
size_t v___x_3068_; size_t v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = lean_usize_of_nat(v___x_3065_);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3063_, v___x_3068_, v___x_3069_, v_x_3062_);
return v___x_3070_;
}
}
else
{
size_t v___x_3071_; size_t v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = ((size_t)0ULL);
v___x_3072_ = lean_usize_of_nat(v___x_3065_);
v___x_3073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3063_, v___x_3071_, v___x_3072_, v_x_3062_);
return v___x_3073_;
}
}
}
else
{
lean_object* v_vs_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v_vs_3074_ = lean_ctor_get(v_x_3061_, 0);
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = lean_array_get_size(v_vs_3074_);
v___x_3077_ = lean_nat_dec_lt(v___x_3075_, v___x_3076_);
if (v___x_3077_ == 0)
{
return v_x_3062_;
}
else
{
uint8_t v___x_3078_; 
v___x_3078_ = lean_nat_dec_le(v___x_3076_, v___x_3076_);
if (v___x_3078_ == 0)
{
if (v___x_3077_ == 0)
{
return v_x_3062_;
}
else
{
size_t v___x_3079_; size_t v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = ((size_t)0ULL);
v___x_3080_ = lean_usize_of_nat(v___x_3076_);
v___x_3081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3074_, v___x_3079_, v___x_3080_, v_x_3062_);
return v___x_3081_;
}
}
else
{
size_t v___x_3082_; size_t v___x_3083_; lean_object* v___x_3084_; 
v___x_3082_ = ((size_t)0ULL);
v___x_3083_ = lean_usize_of_nat(v___x_3076_);
v___x_3084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3074_, v___x_3082_, v___x_3083_, v_x_3062_);
return v___x_3084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3085_, size_t v_i_3086_, size_t v_stop_3087_, lean_object* v_b_3088_){
_start:
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_usize_dec_eq(v_i_3086_, v_stop_3087_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; size_t v___x_3092_; size_t v___x_3093_; 
v___x_3090_ = lean_array_uget_borrowed(v_as_3085_, v_i_3086_);
v___x_3091_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3090_, v_b_3088_);
v___x_3092_ = ((size_t)1ULL);
v___x_3093_ = lean_usize_add(v_i_3086_, v___x_3092_);
v_i_3086_ = v___x_3093_;
v_b_3088_ = v___x_3091_;
goto _start;
}
else
{
return v_b_3088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3095_, lean_object* v_i_3096_, lean_object* v_stop_3097_, lean_object* v_b_3098_){
_start:
{
size_t v_i_boxed_3099_; size_t v_stop_boxed_3100_; lean_object* v_res_3101_; 
v_i_boxed_3099_ = lean_unbox_usize(v_i_3096_);
lean_dec(v_i_3096_);
v_stop_boxed_3100_ = lean_unbox_usize(v_stop_3097_);
lean_dec(v_stop_3097_);
v_res_3101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3095_, v_i_boxed_3099_, v_stop_boxed_3100_, v_b_3098_);
lean_dec_ref(v_as_3095_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3102_, lean_object* v_x_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3102_, v_x_3103_);
lean_dec_ref(v_x_3102_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3105_, size_t v_x_3106_, size_t v_x_3107_, lean_object* v_x_3108_){
_start:
{
if (lean_obj_tag(v_x_3105_) == 0)
{
lean_object* v_cs_3109_; lean_object* v___x_3110_; size_t v___x_3111_; lean_object* v_j_3112_; lean_object* v___x_3113_; size_t v___x_3114_; size_t v___x_3115_; size_t v___x_3116_; size_t v___x_3117_; size_t v___x_3118_; size_t v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
v_cs_3109_ = lean_ctor_get(v_x_3105_, 0);
v___x_3110_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3111_ = lean_usize_shift_right(v_x_3106_, v_x_3107_);
v_j_3112_ = lean_usize_to_nat(v___x_3111_);
v___x_3113_ = lean_array_get_borrowed(v___x_3110_, v_cs_3109_, v_j_3112_);
v___x_3114_ = ((size_t)1ULL);
v___x_3115_ = lean_usize_shift_left(v___x_3114_, v_x_3107_);
v___x_3116_ = lean_usize_sub(v___x_3115_, v___x_3114_);
v___x_3117_ = lean_usize_land(v_x_3106_, v___x_3116_);
v___x_3118_ = ((size_t)5ULL);
v___x_3119_ = lean_usize_sub(v_x_3107_, v___x_3118_);
v___x_3120_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3113_, v___x_3117_, v___x_3119_, v_x_3108_);
v___x_3121_ = lean_unsigned_to_nat(1u);
v___x_3122_ = lean_nat_add(v_j_3112_, v___x_3121_);
lean_dec(v_j_3112_);
v___x_3123_ = lean_array_get_size(v_cs_3109_);
v___x_3124_ = lean_nat_dec_lt(v___x_3122_, v___x_3123_);
if (v___x_3124_ == 0)
{
lean_dec(v___x_3122_);
return v___x_3120_;
}
else
{
uint8_t v___x_3125_; 
v___x_3125_ = lean_nat_dec_le(v___x_3123_, v___x_3123_);
if (v___x_3125_ == 0)
{
if (v___x_3124_ == 0)
{
lean_dec(v___x_3122_);
return v___x_3120_;
}
else
{
size_t v___x_3126_; size_t v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = lean_usize_of_nat(v___x_3122_);
lean_dec(v___x_3122_);
v___x_3127_ = lean_usize_of_nat(v___x_3123_);
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3109_, v___x_3126_, v___x_3127_, v___x_3120_);
return v___x_3128_;
}
}
else
{
size_t v___x_3129_; size_t v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = lean_usize_of_nat(v___x_3122_);
lean_dec(v___x_3122_);
v___x_3130_ = lean_usize_of_nat(v___x_3123_);
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3109_, v___x_3129_, v___x_3130_, v___x_3120_);
return v___x_3131_;
}
}
}
else
{
lean_object* v_vs_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; uint8_t v___x_3135_; 
v_vs_3132_ = lean_ctor_get(v_x_3105_, 0);
v___x_3133_ = lean_usize_to_nat(v_x_3106_);
v___x_3134_ = lean_array_get_size(v_vs_3132_);
v___x_3135_ = lean_nat_dec_lt(v___x_3133_, v___x_3134_);
if (v___x_3135_ == 0)
{
lean_dec(v___x_3133_);
return v_x_3108_;
}
else
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_nat_dec_le(v___x_3134_, v___x_3134_);
if (v___x_3136_ == 0)
{
if (v___x_3135_ == 0)
{
lean_dec(v___x_3133_);
return v_x_3108_;
}
else
{
size_t v___x_3137_; size_t v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_usize_of_nat(v___x_3133_);
lean_dec(v___x_3133_);
v___x_3138_ = lean_usize_of_nat(v___x_3134_);
v___x_3139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3132_, v___x_3137_, v___x_3138_, v_x_3108_);
return v___x_3139_;
}
}
else
{
size_t v___x_3140_; size_t v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = lean_usize_of_nat(v___x_3133_);
lean_dec(v___x_3133_);
v___x_3141_ = lean_usize_of_nat(v___x_3134_);
v___x_3142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3132_, v___x_3140_, v___x_3141_, v_x_3108_);
return v___x_3142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3143_, lean_object* v_x_3144_, lean_object* v_x_3145_, lean_object* v_x_3146_){
_start:
{
size_t v_x_1557__boxed_3147_; size_t v_x_1558__boxed_3148_; lean_object* v_res_3149_; 
v_x_1557__boxed_3147_ = lean_unbox_usize(v_x_3144_);
lean_dec(v_x_3144_);
v_x_1558__boxed_3148_ = lean_unbox_usize(v_x_3145_);
lean_dec(v_x_3145_);
v_res_3149_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3143_, v_x_1557__boxed_3147_, v_x_1558__boxed_3148_, v_x_3146_);
lean_dec_ref(v_x_3143_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3150_, lean_object* v_init_3151_, lean_object* v_start_3152_){
_start:
{
lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = lean_nat_dec_eq(v_start_3152_, v___x_3153_);
if (v___x_3154_ == 0)
{
lean_object* v_root_3155_; lean_object* v_tail_3156_; size_t v_shift_3157_; lean_object* v_tailOff_3158_; uint8_t v___x_3159_; 
v_root_3155_ = lean_ctor_get(v_t_3150_, 0);
v_tail_3156_ = lean_ctor_get(v_t_3150_, 1);
v_shift_3157_ = lean_ctor_get_usize(v_t_3150_, 4);
v_tailOff_3158_ = lean_ctor_get(v_t_3150_, 3);
v___x_3159_ = lean_nat_dec_le(v_tailOff_3158_, v_start_3152_);
if (v___x_3159_ == 0)
{
size_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3160_ = lean_usize_of_nat(v_start_3152_);
v___x_3161_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3155_, v___x_3160_, v_shift_3157_, v_init_3151_);
v___x_3162_ = lean_array_get_size(v_tail_3156_);
v___x_3163_ = lean_nat_dec_lt(v___x_3153_, v___x_3162_);
if (v___x_3163_ == 0)
{
return v___x_3161_;
}
else
{
uint8_t v___x_3164_; 
v___x_3164_ = lean_nat_dec_le(v___x_3162_, v___x_3162_);
if (v___x_3164_ == 0)
{
if (v___x_3163_ == 0)
{
return v___x_3161_;
}
else
{
size_t v___x_3165_; size_t v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = ((size_t)0ULL);
v___x_3166_ = lean_usize_of_nat(v___x_3162_);
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3156_, v___x_3165_, v___x_3166_, v___x_3161_);
return v___x_3167_;
}
}
else
{
size_t v___x_3168_; size_t v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = ((size_t)0ULL);
v___x_3169_ = lean_usize_of_nat(v___x_3162_);
v___x_3170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3156_, v___x_3168_, v___x_3169_, v___x_3161_);
return v___x_3170_;
}
}
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; 
v___x_3171_ = lean_nat_sub(v_start_3152_, v_tailOff_3158_);
v___x_3172_ = lean_array_get_size(v_tail_3156_);
v___x_3173_ = lean_nat_dec_lt(v___x_3171_, v___x_3172_);
if (v___x_3173_ == 0)
{
lean_dec(v___x_3171_);
return v_init_3151_;
}
else
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_nat_dec_le(v___x_3172_, v___x_3172_);
if (v___x_3174_ == 0)
{
if (v___x_3173_ == 0)
{
lean_dec(v___x_3171_);
return v_init_3151_;
}
else
{
size_t v___x_3175_; size_t v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = lean_usize_of_nat(v___x_3171_);
lean_dec(v___x_3171_);
v___x_3176_ = lean_usize_of_nat(v___x_3172_);
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3156_, v___x_3175_, v___x_3176_, v_init_3151_);
return v___x_3177_;
}
}
else
{
size_t v___x_3178_; size_t v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = lean_usize_of_nat(v___x_3171_);
lean_dec(v___x_3171_);
v___x_3179_ = lean_usize_of_nat(v___x_3172_);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3156_, v___x_3178_, v___x_3179_, v_init_3151_);
return v___x_3180_;
}
}
}
}
else
{
lean_object* v_root_3181_; lean_object* v_tail_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; 
v_root_3181_ = lean_ctor_get(v_t_3150_, 0);
v_tail_3182_ = lean_ctor_get(v_t_3150_, 1);
v___x_3183_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3181_, v_init_3151_);
v___x_3184_ = lean_array_get_size(v_tail_3182_);
v___x_3185_ = lean_nat_dec_lt(v___x_3153_, v___x_3184_);
if (v___x_3185_ == 0)
{
return v___x_3183_;
}
else
{
uint8_t v___x_3186_; 
v___x_3186_ = lean_nat_dec_le(v___x_3184_, v___x_3184_);
if (v___x_3186_ == 0)
{
if (v___x_3185_ == 0)
{
return v___x_3183_;
}
else
{
size_t v___x_3187_; size_t v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = ((size_t)0ULL);
v___x_3188_ = lean_usize_of_nat(v___x_3184_);
v___x_3189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3182_, v___x_3187_, v___x_3188_, v___x_3183_);
return v___x_3189_;
}
}
else
{
size_t v___x_3190_; size_t v___x_3191_; lean_object* v___x_3192_; 
v___x_3190_ = ((size_t)0ULL);
v___x_3191_ = lean_usize_of_nat(v___x_3184_);
v___x_3192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3182_, v___x_3190_, v___x_3191_, v___x_3183_);
return v___x_3192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3193_, lean_object* v_init_3194_, lean_object* v_start_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3193_, v_init_3194_, v_start_3195_);
lean_dec(v_start_3195_);
lean_dec_ref(v_t_3193_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3197_, lean_object* v_init_3198_, lean_object* v_start_3199_){
_start:
{
lean_object* v_decls_3200_; lean_object* v___x_3201_; 
v_decls_3200_ = lean_ctor_get(v_lctx_3197_, 1);
v___x_3201_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3200_, v_init_3198_, v_start_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3202_, lean_object* v_init_3203_, lean_object* v_start_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3202_, v_init_3203_, v_start_3204_);
lean_dec(v_start_3204_);
lean_dec_ref(v_lctx_3202_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3206_){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = lean_unsigned_to_nat(0u);
v___x_3208_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3206_, v___x_3207_, v___x_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_LocalContext_size(v_lctx_3209_);
lean_dec_ref(v_lctx_3209_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3211_, lean_object* v_x_3212_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = lean_apply_1(v_f_3211_, v_x_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3214_, lean_object* v_f_3215_){
_start:
{
lean_object* v___f_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___f_3216_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3216_, 0, v_f_3215_);
v___x_3217_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3218_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3217_, v_lctx_3214_, v___f_3216_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3219_, lean_object* v_lctx_3220_, lean_object* v_f_3221_){
_start:
{
lean_object* v___f_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___f_3222_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3222_, 0, v_f_3221_);
v___x_3223_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3224_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3223_, v_lctx_3220_, v___f_3222_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3225_, lean_object* v_f_3226_){
_start:
{
lean_object* v___f_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___f_3227_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3227_, 0, v_f_3226_);
v___x_3228_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3229_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3228_, v_lctx_3225_, v___f_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3230_, lean_object* v_lctx_3231_, lean_object* v_f_3232_){
_start:
{
lean_object* v___f_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___f_3233_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3233_, 0, v_f_3232_);
v___x_3234_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3235_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3234_, v_lctx_3231_, v___f_3233_);
return v___x_3235_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3236_, lean_object* v_as_3237_, size_t v_i_3238_, size_t v_stop_3239_){
_start:
{
uint8_t v___x_3240_; 
v___x_3240_ = lean_usize_dec_eq(v_i_3238_, v_stop_3239_);
if (v___x_3240_ == 0)
{
uint8_t v___x_3241_; uint8_t v___y_3243_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v_fvarId_3249_; uint8_t v___x_3250_; 
v___x_3241_ = 1;
v___x_3247_ = lean_array_uget_borrowed(v_as_3237_, v_i_3238_);
v___x_3248_ = l_Lean_Expr_fvarId_x21(v___x_3247_);
v_fvarId_3249_ = lean_ctor_get(v_val_3236_, 1);
v___x_3250_ = l_Lean_instBEqFVarId_beq(v___x_3248_, v_fvarId_3249_);
lean_dec(v___x_3248_);
v___y_3243_ = v___x_3250_;
goto v___jp_3242_;
v___jp_3242_:
{
if (v___y_3243_ == 0)
{
size_t v___x_3244_; size_t v___x_3245_; 
v___x_3244_ = ((size_t)1ULL);
v___x_3245_ = lean_usize_add(v_i_3238_, v___x_3244_);
v_i_3238_ = v___x_3245_;
goto _start;
}
else
{
return v___x_3241_;
}
}
}
else
{
uint8_t v___x_3251_; 
v___x_3251_ = 0;
return v___x_3251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3252_, lean_object* v_as_3253_, lean_object* v_i_3254_, lean_object* v_stop_3255_){
_start:
{
size_t v_i_boxed_3256_; size_t v_stop_boxed_3257_; uint8_t v_res_3258_; lean_object* v_r_3259_; 
v_i_boxed_3256_ = lean_unbox_usize(v_i_3254_);
lean_dec(v_i_3254_);
v_stop_boxed_3257_ = lean_unbox_usize(v_stop_3255_);
lean_dec(v_stop_3255_);
v_res_3258_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3252_, v_as_3253_, v_i_boxed_3256_, v_stop_boxed_3257_);
lean_dec_ref(v_as_3253_);
lean_dec_ref(v_val_3252_);
v_r_3259_ = lean_box(v_res_3258_);
return v_r_3259_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3260_, lean_object* v_a_u2082_3261_, lean_object* v_exceptFVars_3262_, lean_object* v_i_3263_, lean_object* v_j_3264_){
_start:
{
lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v_size_3280_; uint8_t v___x_3281_; 
v_size_3280_ = lean_ctor_get(v_a_u2081_3260_, 2);
v___x_3281_ = lean_nat_dec_lt(v_i_3263_, v_size_3280_);
if (v___x_3281_ == 0)
{
uint8_t v___x_3282_; 
lean_dec(v_j_3264_);
lean_dec(v_i_3263_);
v___x_3282_ = 1;
return v___x_3282_;
}
else
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_box(0);
v___x_3284_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3283_, v_a_u2081_3260_, v_i_3263_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = lean_unsigned_to_nat(1u);
v___x_3286_ = lean_nat_add(v_i_3263_, v___x_3285_);
lean_dec(v_i_3263_);
v_i_3263_ = v___x_3286_;
goto _start;
}
else
{
lean_object* v_val_3288_; uint8_t v___y_3290_; lean_object* v___x_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; 
v_val_3288_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_val_3288_);
lean_dec_ref(v___x_3284_);
v___x_3299_ = lean_unsigned_to_nat(0u);
v___x_3300_ = lean_array_get_size(v_exceptFVars_3262_);
v___x_3301_ = lean_nat_dec_lt(v___x_3299_, v___x_3300_);
if (v___x_3301_ == 0)
{
v___y_3290_ = v___x_3301_;
goto v___jp_3289_;
}
else
{
if (v___x_3301_ == 0)
{
v___y_3290_ = v___x_3301_;
goto v___jp_3289_;
}
else
{
size_t v___x_3302_; size_t v___x_3303_; uint8_t v___x_3304_; 
v___x_3302_ = ((size_t)0ULL);
v___x_3303_ = lean_usize_of_nat(v___x_3300_);
v___x_3304_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3288_, v_exceptFVars_3262_, v___x_3302_, v___x_3303_);
if (v___x_3304_ == 0)
{
v___y_3290_ = v___x_3304_;
goto v___jp_3289_;
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
lean_dec(v_val_3288_);
v___x_3305_ = lean_unsigned_to_nat(1u);
v___x_3306_ = lean_nat_add(v_i_3263_, v___x_3305_);
lean_dec(v_i_3263_);
v_i_3263_ = v___x_3306_;
goto _start;
}
}
}
v___jp_3289_:
{
lean_object* v_size_3291_; uint8_t v___x_3292_; 
v_size_3291_ = lean_ctor_get(v_a_u2082_3261_, 2);
v___x_3292_ = lean_nat_dec_lt(v_j_3264_, v_size_3291_);
if (v___x_3292_ == 0)
{
lean_dec(v_val_3288_);
lean_dec(v_j_3264_);
lean_dec(v_i_3263_);
return v___y_3290_;
}
else
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3283_, v_a_u2082_3261_, v_j_3264_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec(v_val_3288_);
v___x_3294_ = lean_unsigned_to_nat(1u);
v___x_3295_ = lean_nat_add(v_j_3264_, v___x_3294_);
lean_dec(v_j_3264_);
v_j_3264_ = v___x_3295_;
goto _start;
}
else
{
lean_object* v_val_3297_; lean_object* v_fvarId_3298_; 
v_val_3297_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_val_3297_);
lean_dec_ref(v___x_3293_);
v_fvarId_3298_ = lean_ctor_get(v_val_3288_, 1);
lean_inc(v_fvarId_3298_);
lean_dec(v_val_3288_);
v___y_3277_ = v_val_3297_;
v___y_3278_ = v_fvarId_3298_;
goto v___jp_3276_;
}
}
}
}
}
v___jp_3265_:
{
uint8_t v___x_3268_; 
v___x_3268_ = l_Lean_instBEqFVarId_beq(v___y_3266_, v___y_3267_);
lean_dec(v___y_3267_);
lean_dec(v___y_3266_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = lean_unsigned_to_nat(1u);
v___x_3270_ = lean_nat_add(v_j_3264_, v___x_3269_);
lean_dec(v_j_3264_);
v_j_3264_ = v___x_3270_;
goto _start;
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3272_ = lean_unsigned_to_nat(1u);
v___x_3273_ = lean_nat_add(v_i_3263_, v___x_3272_);
lean_dec(v_i_3263_);
v___x_3274_ = lean_nat_add(v_j_3264_, v___x_3272_);
lean_dec(v_j_3264_);
v_i_3263_ = v___x_3273_;
v_j_3264_ = v___x_3274_;
goto _start;
}
}
v___jp_3276_:
{
lean_object* v_fvarId_3279_; 
v_fvarId_3279_ = lean_ctor_get(v___y_3277_, 1);
lean_inc(v_fvarId_3279_);
lean_dec_ref(v___y_3277_);
v___y_3266_ = v___y_3278_;
v___y_3267_ = v_fvarId_3279_;
goto v___jp_3265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3308_, lean_object* v_a_u2082_3309_, lean_object* v_exceptFVars_3310_, lean_object* v_i_3311_, lean_object* v_j_3312_){
_start:
{
uint8_t v_res_3313_; lean_object* v_r_3314_; 
v_res_3313_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3308_, v_a_u2082_3309_, v_exceptFVars_3310_, v_i_3311_, v_j_3312_);
lean_dec_ref(v_exceptFVars_3310_);
lean_dec_ref(v_a_u2082_3309_);
lean_dec_ref(v_a_u2081_3308_);
v_r_3314_ = lean_box(v_res_3313_);
return v_r_3314_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3315_, lean_object* v_lctx_u2082_3316_, lean_object* v_exceptFVars_3317_){
_start:
{
lean_object* v_decls_3318_; lean_object* v_decls_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v_decls_3318_ = lean_ctor_get(v_lctx_u2081_3315_, 1);
v_decls_3319_ = lean_ctor_get(v_lctx_u2082_3316_, 1);
v___x_3320_ = lean_unsigned_to_nat(0u);
v___x_3321_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3318_, v_decls_3319_, v_exceptFVars_3317_, v___x_3320_, v___x_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3322_, lean_object* v_lctx_u2082_3323_, lean_object* v_exceptFVars_3324_){
_start:
{
uint8_t v_res_3325_; lean_object* v_r_3326_; 
v_res_3325_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3322_, v_lctx_u2082_3323_, v_exceptFVars_3324_);
lean_dec_ref(v_exceptFVars_3324_);
lean_dec_ref(v_lctx_u2082_3323_);
lean_dec_ref(v_lctx_u2081_3322_);
v_r_3326_ = lean_box(v_res_3325_);
return v_r_3326_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3328_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3329_ = lean_unsigned_to_nat(14u);
v___x_3330_ = lean_unsigned_to_nat(576u);
v___x_3331_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3332_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3333_ = l_mkPanicMessageWithDecl(v___x_3332_, v___x_3331_, v___x_3330_, v___x_3329_, v___x_3328_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3334_, lean_object* v_lctx_3335_, lean_object* v___x_3336_, uint8_t v_isLambda_3337_, uint8_t v_usedLetOnly_3338_, uint8_t v_generalizeNondepLet_3339_, lean_object* v_i_3340_, lean_object* v_x_3341_, lean_object* v_b_3342_){
_start:
{
lean_object* v_n_3344_; lean_object* v_ty_3345_; uint8_t v_bi_3346_; lean_object* v_x_3350_; lean_object* v___x_3351_; 
v_x_3350_ = lean_array_fget_borrowed(v_xs_3334_, v_i_3340_);
v___x_3351_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3335_, v_x_3350_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec_ref(v_b_3342_);
v___x_3352_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3353_ = l_panic___redArg(v___x_3336_, v___x_3352_);
return v___x_3353_;
}
else
{
lean_object* v_val_3354_; 
v_val_3354_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_val_3354_);
lean_dec_ref(v___x_3351_);
if (lean_obj_tag(v_val_3354_) == 0)
{
lean_object* v_userName_3355_; lean_object* v_type_3356_; uint8_t v_bi_3357_; 
v_userName_3355_ = lean_ctor_get(v_val_3354_, 2);
lean_inc(v_userName_3355_);
v_type_3356_ = lean_ctor_get(v_val_3354_, 3);
lean_inc_ref(v_type_3356_);
v_bi_3357_ = lean_ctor_get_uint8(v_val_3354_, sizeof(void*)*4);
lean_dec_ref(v_val_3354_);
v_n_3344_ = v_userName_3355_;
v_ty_3345_ = v_type_3356_;
v_bi_3346_ = v_bi_3357_;
goto v___jp_3343_;
}
else
{
lean_object* v_userName_3358_; lean_object* v_type_3359_; lean_object* v_value_3360_; uint8_t v_nondep_3361_; uint8_t v___y_3367_; 
v_userName_3358_ = lean_ctor_get(v_val_3354_, 2);
lean_inc(v_userName_3358_);
v_type_3359_ = lean_ctor_get(v_val_3354_, 3);
lean_inc_ref(v_type_3359_);
v_value_3360_ = lean_ctor_get(v_val_3354_, 4);
lean_inc_ref(v_value_3360_);
v_nondep_3361_ = lean_ctor_get_uint8(v_val_3354_, sizeof(void*)*5);
lean_dec_ref(v_val_3354_);
if (v_nondep_3361_ == 0)
{
v___y_3367_ = v_nondep_3361_;
goto v___jp_3366_;
}
else
{
if (v_generalizeNondepLet_3339_ == 0)
{
v___y_3367_ = v_generalizeNondepLet_3339_;
goto v___jp_3366_;
}
else
{
uint8_t v___x_3372_; 
lean_dec_ref(v_value_3360_);
v___x_3372_ = 0;
v_n_3344_ = v_userName_3358_;
v_ty_3345_ = v_type_3359_;
v_bi_3346_ = v___x_3372_;
goto v___jp_3343_;
}
}
v___jp_3362_:
{
lean_object* v_ty_3363_; lean_object* v_val_3364_; lean_object* v___x_3365_; 
v_ty_3363_ = lean_expr_abstract_range(v_type_3359_, v_i_3340_, v_xs_3334_);
lean_dec_ref(v_type_3359_);
v_val_3364_ = lean_expr_abstract_range(v_value_3360_, v_i_3340_, v_xs_3334_);
lean_dec_ref(v_value_3360_);
v___x_3365_ = l_Lean_Expr_letE___override(v_userName_3358_, v_ty_3363_, v_val_3364_, v_b_3342_, v_nondep_3361_);
return v___x_3365_;
}
v___jp_3366_:
{
if (v_usedLetOnly_3338_ == 0)
{
goto v___jp_3362_;
}
else
{
if (v___y_3367_ == 0)
{
lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3368_ = lean_unsigned_to_nat(0u);
v___x_3369_ = lean_expr_has_loose_bvar(v_b_3342_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
lean_dec_ref(v_value_3360_);
lean_dec_ref(v_type_3359_);
lean_dec(v_userName_3358_);
v___x_3370_ = lean_unsigned_to_nat(1u);
v___x_3371_ = lean_expr_lower_loose_bvars(v_b_3342_, v___x_3370_, v___x_3370_);
lean_dec_ref(v_b_3342_);
return v___x_3371_;
}
else
{
goto v___jp_3362_;
}
}
else
{
goto v___jp_3362_;
}
}
}
}
}
v___jp_3343_:
{
lean_object* v_ty_3347_; 
v_ty_3347_ = lean_expr_abstract_range(v_ty_3345_, v_i_3340_, v_xs_3334_);
lean_dec_ref(v_ty_3345_);
if (v_isLambda_3337_ == 0)
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Lean_mkForall(v_n_3344_, v_bi_3346_, v_ty_3347_, v_b_3342_);
return v___x_3348_;
}
else
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_mkLambda(v_n_3344_, v_bi_3346_, v_ty_3347_, v_b_3342_);
return v___x_3349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3373_, lean_object* v_lctx_3374_, lean_object* v___x_3375_, lean_object* v_isLambda_3376_, lean_object* v_usedLetOnly_3377_, lean_object* v_generalizeNondepLet_3378_, lean_object* v_i_3379_, lean_object* v_x_3380_, lean_object* v_b_3381_){
_start:
{
uint8_t v_isLambda_boxed_3382_; uint8_t v_usedLetOnly_boxed_3383_; uint8_t v_generalizeNondepLet_boxed_3384_; lean_object* v_res_3385_; 
v_isLambda_boxed_3382_ = lean_unbox(v_isLambda_3376_);
v_usedLetOnly_boxed_3383_ = lean_unbox(v_usedLetOnly_3377_);
v_generalizeNondepLet_boxed_3384_ = lean_unbox(v_generalizeNondepLet_3378_);
v_res_3385_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3373_, v_lctx_3374_, v___x_3375_, v_isLambda_boxed_3382_, v_usedLetOnly_boxed_3383_, v_generalizeNondepLet_boxed_3384_, v_i_3379_, v_x_3380_, v_b_3381_);
lean_dec(v_i_3379_);
lean_dec_ref(v___x_3375_);
lean_dec_ref(v_xs_3373_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3386_, lean_object* v_lctx_3387_, lean_object* v_xs_3388_, lean_object* v_b_3389_, uint8_t v_usedLetOnly_3390_, uint8_t v_generalizeNondepLet_3391_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___f_3396_; lean_object* v_b_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3392_ = l_Lean_instInhabitedExpr;
v___x_3393_ = lean_box(v_isLambda_3386_);
v___x_3394_ = lean_box(v_usedLetOnly_3390_);
v___x_3395_ = lean_box(v_generalizeNondepLet_3391_);
lean_inc_ref(v_xs_3388_);
v___f_3396_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3396_, 0, v_xs_3388_);
lean_closure_set(v___f_3396_, 1, v_lctx_3387_);
lean_closure_set(v___f_3396_, 2, v___x_3392_);
lean_closure_set(v___f_3396_, 3, v___x_3393_);
lean_closure_set(v___f_3396_, 4, v___x_3394_);
lean_closure_set(v___f_3396_, 5, v___x_3395_);
v_b_3397_ = lean_expr_abstract(v_b_3389_, v_xs_3388_);
v___x_3398_ = lean_array_get_size(v_xs_3388_);
lean_dec_ref(v_xs_3388_);
v___x_3399_ = l_Nat_foldRev___redArg(v___x_3398_, v___f_3396_, v_b_3397_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3400_, lean_object* v_lctx_3401_, lean_object* v_xs_3402_, lean_object* v_b_3403_, lean_object* v_usedLetOnly_3404_, lean_object* v_generalizeNondepLet_3405_){
_start:
{
uint8_t v_isLambda_boxed_3406_; uint8_t v_usedLetOnly_boxed_3407_; uint8_t v_generalizeNondepLet_boxed_3408_; lean_object* v_res_3409_; 
v_isLambda_boxed_3406_ = lean_unbox(v_isLambda_3400_);
v_usedLetOnly_boxed_3407_ = lean_unbox(v_usedLetOnly_3404_);
v_generalizeNondepLet_boxed_3408_ = lean_unbox(v_generalizeNondepLet_3405_);
v_res_3409_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3406_, v_lctx_3401_, v_xs_3402_, v_b_3403_, v_usedLetOnly_boxed_3407_, v_generalizeNondepLet_boxed_3408_);
lean_dec_ref(v_b_3403_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3410_, lean_object* v_lctx_3411_, uint8_t v_usedLetOnly_3412_, uint8_t v_generalizeNondepLet_3413_, lean_object* v_x_3414_, lean_object* v_x_3415_){
_start:
{
lean_object* v_zero_3416_; uint8_t v_isZero_3417_; 
v_zero_3416_ = lean_unsigned_to_nat(0u);
v_isZero_3417_ = lean_nat_dec_eq(v_x_3414_, v_zero_3416_);
if (v_isZero_3417_ == 1)
{
lean_dec(v_x_3414_);
lean_dec_ref(v_lctx_3411_);
return v_x_3415_;
}
else
{
lean_object* v_one_3418_; lean_object* v_n_3419_; lean_object* v_n_3421_; lean_object* v_ty_3422_; uint8_t v_bi_3423_; lean_object* v_x_3427_; lean_object* v___x_3428_; 
v_one_3418_ = lean_unsigned_to_nat(1u);
v_n_3419_ = lean_nat_sub(v_x_3414_, v_one_3418_);
lean_dec(v_x_3414_);
v_x_3427_ = lean_array_fget_borrowed(v_xs_3410_, v_n_3419_);
lean_inc_ref(v_lctx_3411_);
v___x_3428_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3411_, v_x_3427_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
lean_dec_ref(v_x_3415_);
v___x_3429_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3430_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3429_);
v_x_3414_ = v_n_3419_;
v_x_3415_ = v___x_3430_;
goto _start;
}
else
{
lean_object* v_val_3432_; 
v_val_3432_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_val_3432_);
lean_dec_ref(v___x_3428_);
if (lean_obj_tag(v_val_3432_) == 0)
{
lean_object* v_userName_3433_; lean_object* v_type_3434_; uint8_t v_bi_3435_; 
v_userName_3433_ = lean_ctor_get(v_val_3432_, 2);
lean_inc(v_userName_3433_);
v_type_3434_ = lean_ctor_get(v_val_3432_, 3);
lean_inc_ref(v_type_3434_);
v_bi_3435_ = lean_ctor_get_uint8(v_val_3432_, sizeof(void*)*4);
lean_dec_ref(v_val_3432_);
v_n_3421_ = v_userName_3433_;
v_ty_3422_ = v_type_3434_;
v_bi_3423_ = v_bi_3435_;
goto v___jp_3420_;
}
else
{
lean_object* v_userName_3436_; lean_object* v_type_3437_; lean_object* v_value_3438_; uint8_t v_nondep_3439_; uint8_t v___y_3446_; 
v_userName_3436_ = lean_ctor_get(v_val_3432_, 2);
lean_inc(v_userName_3436_);
v_type_3437_ = lean_ctor_get(v_val_3432_, 3);
lean_inc_ref(v_type_3437_);
v_value_3438_ = lean_ctor_get(v_val_3432_, 4);
lean_inc_ref(v_value_3438_);
v_nondep_3439_ = lean_ctor_get_uint8(v_val_3432_, sizeof(void*)*5);
lean_dec_ref(v_val_3432_);
if (v_nondep_3439_ == 0)
{
v___y_3446_ = v_nondep_3439_;
goto v___jp_3445_;
}
else
{
if (v_generalizeNondepLet_3413_ == 0)
{
v___y_3446_ = v_generalizeNondepLet_3413_;
goto v___jp_3445_;
}
else
{
uint8_t v___x_3450_; 
lean_dec_ref(v_value_3438_);
v___x_3450_ = 0;
v_n_3421_ = v_userName_3436_;
v_ty_3422_ = v_type_3437_;
v_bi_3423_ = v___x_3450_;
goto v___jp_3420_;
}
}
v___jp_3440_:
{
lean_object* v_ty_3441_; lean_object* v_val_3442_; lean_object* v___x_3443_; 
v_ty_3441_ = lean_expr_abstract_range(v_type_3437_, v_n_3419_, v_xs_3410_);
lean_dec_ref(v_type_3437_);
v_val_3442_ = lean_expr_abstract_range(v_value_3438_, v_n_3419_, v_xs_3410_);
lean_dec_ref(v_value_3438_);
v___x_3443_ = l_Lean_Expr_letE___override(v_userName_3436_, v_ty_3441_, v_val_3442_, v_x_3415_, v_nondep_3439_);
v_x_3414_ = v_n_3419_;
v_x_3415_ = v___x_3443_;
goto _start;
}
v___jp_3445_:
{
if (v_usedLetOnly_3412_ == 0)
{
goto v___jp_3440_;
}
else
{
if (v___y_3446_ == 0)
{
uint8_t v___x_3447_; 
v___x_3447_ = lean_expr_has_loose_bvar(v_x_3415_, v_zero_3416_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; 
lean_dec_ref(v_value_3438_);
lean_dec_ref(v_type_3437_);
lean_dec(v_userName_3436_);
v___x_3448_ = lean_expr_lower_loose_bvars(v_x_3415_, v_one_3418_, v_one_3418_);
lean_dec_ref(v_x_3415_);
v_x_3414_ = v_n_3419_;
v_x_3415_ = v___x_3448_;
goto _start;
}
else
{
goto v___jp_3440_;
}
}
else
{
goto v___jp_3440_;
}
}
}
}
}
v___jp_3420_:
{
lean_object* v_ty_3424_; lean_object* v___x_3425_; 
v_ty_3424_ = lean_expr_abstract_range(v_ty_3422_, v_n_3419_, v_xs_3410_);
lean_dec_ref(v_ty_3422_);
v___x_3425_ = l_Lean_mkLambda(v_n_3421_, v_bi_3423_, v_ty_3424_, v_x_3415_);
v_x_3414_ = v_n_3419_;
v_x_3415_ = v___x_3425_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3451_, lean_object* v_lctx_3452_, lean_object* v_usedLetOnly_3453_, lean_object* v_generalizeNondepLet_3454_, lean_object* v_x_3455_, lean_object* v_x_3456_){
_start:
{
uint8_t v_usedLetOnly_boxed_3457_; uint8_t v_generalizeNondepLet_boxed_3458_; lean_object* v_res_3459_; 
v_usedLetOnly_boxed_3457_ = lean_unbox(v_usedLetOnly_3453_);
v_generalizeNondepLet_boxed_3458_ = lean_unbox(v_generalizeNondepLet_3454_);
v_res_3459_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3451_, v_lctx_3452_, v_usedLetOnly_boxed_3457_, v_generalizeNondepLet_boxed_3458_, v_x_3455_, v_x_3456_);
lean_dec_ref(v_xs_3451_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3460_, lean_object* v_lctx_3461_, uint8_t v_usedLetOnly_3462_, uint8_t v_generalizeNondepLet_3463_, lean_object* v_x_3464_, lean_object* v_x_3465_){
_start:
{
lean_object* v_zero_3466_; uint8_t v_isZero_3467_; 
v_zero_3466_ = lean_unsigned_to_nat(0u);
v_isZero_3467_ = lean_nat_dec_eq(v_x_3464_, v_zero_3466_);
if (v_isZero_3467_ == 1)
{
lean_dec_ref(v_lctx_3461_);
return v_x_3465_;
}
else
{
lean_object* v_one_3468_; lean_object* v_n_3469_; lean_object* v_n_3471_; lean_object* v_ty_3472_; uint8_t v_bi_3473_; lean_object* v_x_3477_; lean_object* v___x_3478_; 
v_one_3468_ = lean_unsigned_to_nat(1u);
v_n_3469_ = lean_nat_sub(v_x_3464_, v_one_3468_);
v_x_3477_ = lean_array_fget_borrowed(v_xs_3460_, v_n_3469_);
lean_inc_ref(v_lctx_3461_);
v___x_3478_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3461_, v_x_3477_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
lean_dec_ref(v_x_3465_);
v___x_3479_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3480_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3479_);
v___x_3481_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3460_, v_lctx_3461_, v_usedLetOnly_3462_, v_generalizeNondepLet_3463_, v_n_3469_, v___x_3480_);
return v___x_3481_;
}
else
{
lean_object* v_val_3482_; 
v_val_3482_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_val_3482_);
lean_dec_ref(v___x_3478_);
if (lean_obj_tag(v_val_3482_) == 0)
{
lean_object* v_userName_3483_; lean_object* v_type_3484_; uint8_t v_bi_3485_; 
v_userName_3483_ = lean_ctor_get(v_val_3482_, 2);
lean_inc(v_userName_3483_);
v_type_3484_ = lean_ctor_get(v_val_3482_, 3);
lean_inc_ref(v_type_3484_);
v_bi_3485_ = lean_ctor_get_uint8(v_val_3482_, sizeof(void*)*4);
lean_dec_ref(v_val_3482_);
v_n_3471_ = v_userName_3483_;
v_ty_3472_ = v_type_3484_;
v_bi_3473_ = v_bi_3485_;
goto v___jp_3470_;
}
else
{
lean_object* v_userName_3486_; lean_object* v_type_3487_; lean_object* v_value_3488_; uint8_t v_nondep_3489_; uint8_t v___y_3496_; 
v_userName_3486_ = lean_ctor_get(v_val_3482_, 2);
lean_inc(v_userName_3486_);
v_type_3487_ = lean_ctor_get(v_val_3482_, 3);
lean_inc_ref(v_type_3487_);
v_value_3488_ = lean_ctor_get(v_val_3482_, 4);
lean_inc_ref(v_value_3488_);
v_nondep_3489_ = lean_ctor_get_uint8(v_val_3482_, sizeof(void*)*5);
lean_dec_ref(v_val_3482_);
if (v_nondep_3489_ == 0)
{
v___y_3496_ = v_nondep_3489_;
goto v___jp_3495_;
}
else
{
if (v_generalizeNondepLet_3463_ == 0)
{
v___y_3496_ = v_generalizeNondepLet_3463_;
goto v___jp_3495_;
}
else
{
uint8_t v___x_3500_; 
lean_dec_ref(v_value_3488_);
v___x_3500_ = 0;
v_n_3471_ = v_userName_3486_;
v_ty_3472_ = v_type_3487_;
v_bi_3473_ = v___x_3500_;
goto v___jp_3470_;
}
}
v___jp_3490_:
{
lean_object* v_ty_3491_; lean_object* v_val_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v_ty_3491_ = lean_expr_abstract_range(v_type_3487_, v_n_3469_, v_xs_3460_);
lean_dec_ref(v_type_3487_);
v_val_3492_ = lean_expr_abstract_range(v_value_3488_, v_n_3469_, v_xs_3460_);
lean_dec_ref(v_value_3488_);
v___x_3493_ = l_Lean_Expr_letE___override(v_userName_3486_, v_ty_3491_, v_val_3492_, v_x_3465_, v_nondep_3489_);
v___x_3494_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3460_, v_lctx_3461_, v_usedLetOnly_3462_, v_generalizeNondepLet_3463_, v_n_3469_, v___x_3493_);
return v___x_3494_;
}
v___jp_3495_:
{
if (v_usedLetOnly_3462_ == 0)
{
goto v___jp_3490_;
}
else
{
if (v___y_3496_ == 0)
{
uint8_t v___x_3497_; 
v___x_3497_ = lean_expr_has_loose_bvar(v_x_3465_, v_zero_3466_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_dec_ref(v_value_3488_);
lean_dec_ref(v_type_3487_);
lean_dec(v_userName_3486_);
v___x_3498_ = lean_expr_lower_loose_bvars(v_x_3465_, v_one_3468_, v_one_3468_);
lean_dec_ref(v_x_3465_);
v___x_3499_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3460_, v_lctx_3461_, v_usedLetOnly_3462_, v_generalizeNondepLet_3463_, v_n_3469_, v___x_3498_);
return v___x_3499_;
}
else
{
goto v___jp_3490_;
}
}
else
{
goto v___jp_3490_;
}
}
}
}
}
v___jp_3470_:
{
lean_object* v_ty_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v_ty_3474_ = lean_expr_abstract_range(v_ty_3472_, v_n_3469_, v_xs_3460_);
lean_dec_ref(v_ty_3472_);
v___x_3475_ = l_Lean_mkLambda(v_n_3471_, v_bi_3473_, v_ty_3474_, v_x_3465_);
v___x_3476_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3460_, v_lctx_3461_, v_usedLetOnly_3462_, v_generalizeNondepLet_3463_, v_n_3469_, v___x_3475_);
return v___x_3476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3501_, lean_object* v_lctx_3502_, lean_object* v_usedLetOnly_3503_, lean_object* v_generalizeNondepLet_3504_, lean_object* v_x_3505_, lean_object* v_x_3506_){
_start:
{
uint8_t v_usedLetOnly_boxed_3507_; uint8_t v_generalizeNondepLet_boxed_3508_; lean_object* v_res_3509_; 
v_usedLetOnly_boxed_3507_ = lean_unbox(v_usedLetOnly_3503_);
v_generalizeNondepLet_boxed_3508_ = lean_unbox(v_generalizeNondepLet_3504_);
v_res_3509_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3501_, v_lctx_3502_, v_usedLetOnly_boxed_3507_, v_generalizeNondepLet_boxed_3508_, v_x_3505_, v_x_3506_);
lean_dec(v_x_3505_);
lean_dec_ref(v_xs_3501_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3510_, lean_object* v_xs_3511_, lean_object* v_b_3512_, uint8_t v_usedLetOnly_3513_, uint8_t v_generalizeNondepLet_3514_){
_start:
{
lean_object* v_b_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v_b_3515_ = lean_expr_abstract(v_b_3512_, v_xs_3511_);
v___x_3516_ = lean_array_get_size(v_xs_3511_);
v___x_3517_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3511_, v_lctx_3510_, v_usedLetOnly_3513_, v_generalizeNondepLet_3514_, v___x_3516_, v_b_3515_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3518_, lean_object* v_xs_3519_, lean_object* v_b_3520_, lean_object* v_usedLetOnly_3521_, lean_object* v_generalizeNondepLet_3522_){
_start:
{
uint8_t v_usedLetOnly_boxed_3523_; uint8_t v_generalizeNondepLet_boxed_3524_; lean_object* v_res_3525_; 
v_usedLetOnly_boxed_3523_ = lean_unbox(v_usedLetOnly_3521_);
v_generalizeNondepLet_boxed_3524_ = lean_unbox(v_generalizeNondepLet_3522_);
v_res_3525_ = l_Lean_LocalContext_mkLambda(v_lctx_3518_, v_xs_3519_, v_b_3520_, v_usedLetOnly_boxed_3523_, v_generalizeNondepLet_boxed_3524_);
lean_dec_ref(v_b_3520_);
lean_dec_ref(v_xs_3519_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3526_, lean_object* v_lctx_3527_, uint8_t v_usedLetOnly_3528_, uint8_t v_generalizeNondepLet_3529_, lean_object* v_x_3530_, lean_object* v_x_3531_){
_start:
{
lean_object* v_zero_3532_; uint8_t v_isZero_3533_; 
v_zero_3532_ = lean_unsigned_to_nat(0u);
v_isZero_3533_ = lean_nat_dec_eq(v_x_3530_, v_zero_3532_);
if (v_isZero_3533_ == 1)
{
lean_dec(v_x_3530_);
lean_dec_ref(v_lctx_3527_);
return v_x_3531_;
}
else
{
lean_object* v_one_3534_; lean_object* v_n_3535_; lean_object* v_n_3537_; lean_object* v_ty_3538_; uint8_t v_bi_3539_; lean_object* v_x_3543_; lean_object* v___x_3544_; 
v_one_3534_ = lean_unsigned_to_nat(1u);
v_n_3535_ = lean_nat_sub(v_x_3530_, v_one_3534_);
lean_dec(v_x_3530_);
v_x_3543_ = lean_array_fget_borrowed(v_xs_3526_, v_n_3535_);
lean_inc_ref(v_lctx_3527_);
v___x_3544_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3527_, v_x_3543_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec_ref(v_x_3531_);
v___x_3545_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3546_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3545_);
v_x_3530_ = v_n_3535_;
v_x_3531_ = v___x_3546_;
goto _start;
}
else
{
lean_object* v_val_3548_; 
v_val_3548_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_val_3548_);
lean_dec_ref(v___x_3544_);
if (lean_obj_tag(v_val_3548_) == 0)
{
lean_object* v_userName_3549_; lean_object* v_type_3550_; uint8_t v_bi_3551_; 
v_userName_3549_ = lean_ctor_get(v_val_3548_, 2);
lean_inc(v_userName_3549_);
v_type_3550_ = lean_ctor_get(v_val_3548_, 3);
lean_inc_ref(v_type_3550_);
v_bi_3551_ = lean_ctor_get_uint8(v_val_3548_, sizeof(void*)*4);
lean_dec_ref(v_val_3548_);
v_n_3537_ = v_userName_3549_;
v_ty_3538_ = v_type_3550_;
v_bi_3539_ = v_bi_3551_;
goto v___jp_3536_;
}
else
{
lean_object* v_userName_3552_; lean_object* v_type_3553_; lean_object* v_value_3554_; uint8_t v_nondep_3555_; uint8_t v___y_3562_; 
v_userName_3552_ = lean_ctor_get(v_val_3548_, 2);
lean_inc(v_userName_3552_);
v_type_3553_ = lean_ctor_get(v_val_3548_, 3);
lean_inc_ref(v_type_3553_);
v_value_3554_ = lean_ctor_get(v_val_3548_, 4);
lean_inc_ref(v_value_3554_);
v_nondep_3555_ = lean_ctor_get_uint8(v_val_3548_, sizeof(void*)*5);
lean_dec_ref(v_val_3548_);
if (v_nondep_3555_ == 0)
{
v___y_3562_ = v_nondep_3555_;
goto v___jp_3561_;
}
else
{
if (v_generalizeNondepLet_3529_ == 0)
{
v___y_3562_ = v_generalizeNondepLet_3529_;
goto v___jp_3561_;
}
else
{
uint8_t v___x_3566_; 
lean_dec_ref(v_value_3554_);
v___x_3566_ = 0;
v_n_3537_ = v_userName_3552_;
v_ty_3538_ = v_type_3553_;
v_bi_3539_ = v___x_3566_;
goto v___jp_3536_;
}
}
v___jp_3556_:
{
lean_object* v_ty_3557_; lean_object* v_val_3558_; lean_object* v___x_3559_; 
v_ty_3557_ = lean_expr_abstract_range(v_type_3553_, v_n_3535_, v_xs_3526_);
lean_dec_ref(v_type_3553_);
v_val_3558_ = lean_expr_abstract_range(v_value_3554_, v_n_3535_, v_xs_3526_);
lean_dec_ref(v_value_3554_);
v___x_3559_ = l_Lean_Expr_letE___override(v_userName_3552_, v_ty_3557_, v_val_3558_, v_x_3531_, v_nondep_3555_);
v_x_3530_ = v_n_3535_;
v_x_3531_ = v___x_3559_;
goto _start;
}
v___jp_3561_:
{
if (v_usedLetOnly_3528_ == 0)
{
goto v___jp_3556_;
}
else
{
if (v___y_3562_ == 0)
{
uint8_t v___x_3563_; 
v___x_3563_ = lean_expr_has_loose_bvar(v_x_3531_, v_zero_3532_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; 
lean_dec_ref(v_value_3554_);
lean_dec_ref(v_type_3553_);
lean_dec(v_userName_3552_);
v___x_3564_ = lean_expr_lower_loose_bvars(v_x_3531_, v_one_3534_, v_one_3534_);
lean_dec_ref(v_x_3531_);
v_x_3530_ = v_n_3535_;
v_x_3531_ = v___x_3564_;
goto _start;
}
else
{
goto v___jp_3556_;
}
}
else
{
goto v___jp_3556_;
}
}
}
}
}
v___jp_3536_:
{
lean_object* v_ty_3540_; lean_object* v___x_3541_; 
v_ty_3540_ = lean_expr_abstract_range(v_ty_3538_, v_n_3535_, v_xs_3526_);
lean_dec_ref(v_ty_3538_);
v___x_3541_ = l_Lean_mkForall(v_n_3537_, v_bi_3539_, v_ty_3540_, v_x_3531_);
v_x_3530_ = v_n_3535_;
v_x_3531_ = v___x_3541_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3567_, lean_object* v_lctx_3568_, lean_object* v_usedLetOnly_3569_, lean_object* v_generalizeNondepLet_3570_, lean_object* v_x_3571_, lean_object* v_x_3572_){
_start:
{
uint8_t v_usedLetOnly_boxed_3573_; uint8_t v_generalizeNondepLet_boxed_3574_; lean_object* v_res_3575_; 
v_usedLetOnly_boxed_3573_ = lean_unbox(v_usedLetOnly_3569_);
v_generalizeNondepLet_boxed_3574_ = lean_unbox(v_generalizeNondepLet_3570_);
v_res_3575_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3567_, v_lctx_3568_, v_usedLetOnly_boxed_3573_, v_generalizeNondepLet_boxed_3574_, v_x_3571_, v_x_3572_);
lean_dec_ref(v_xs_3567_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3576_, lean_object* v_lctx_3577_, uint8_t v_usedLetOnly_3578_, uint8_t v_generalizeNondepLet_3579_, lean_object* v_x_3580_, lean_object* v_x_3581_){
_start:
{
lean_object* v_zero_3582_; uint8_t v_isZero_3583_; 
v_zero_3582_ = lean_unsigned_to_nat(0u);
v_isZero_3583_ = lean_nat_dec_eq(v_x_3580_, v_zero_3582_);
if (v_isZero_3583_ == 1)
{
lean_dec_ref(v_lctx_3577_);
return v_x_3581_;
}
else
{
lean_object* v_one_3584_; lean_object* v_n_3585_; lean_object* v_n_3587_; lean_object* v_ty_3588_; uint8_t v_bi_3589_; lean_object* v_x_3593_; lean_object* v___x_3594_; 
v_one_3584_ = lean_unsigned_to_nat(1u);
v_n_3585_ = lean_nat_sub(v_x_3580_, v_one_3584_);
v_x_3593_ = lean_array_fget_borrowed(v_xs_3576_, v_n_3585_);
lean_inc_ref(v_lctx_3577_);
v___x_3594_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3577_, v_x_3593_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
lean_dec_ref(v_x_3581_);
v___x_3595_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3596_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3595_);
v___x_3597_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3576_, v_lctx_3577_, v_usedLetOnly_3578_, v_generalizeNondepLet_3579_, v_n_3585_, v___x_3596_);
return v___x_3597_;
}
else
{
lean_object* v_val_3598_; 
v_val_3598_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_val_3598_);
lean_dec_ref(v___x_3594_);
if (lean_obj_tag(v_val_3598_) == 0)
{
lean_object* v_userName_3599_; lean_object* v_type_3600_; uint8_t v_bi_3601_; 
v_userName_3599_ = lean_ctor_get(v_val_3598_, 2);
lean_inc(v_userName_3599_);
v_type_3600_ = lean_ctor_get(v_val_3598_, 3);
lean_inc_ref(v_type_3600_);
v_bi_3601_ = lean_ctor_get_uint8(v_val_3598_, sizeof(void*)*4);
lean_dec_ref(v_val_3598_);
v_n_3587_ = v_userName_3599_;
v_ty_3588_ = v_type_3600_;
v_bi_3589_ = v_bi_3601_;
goto v___jp_3586_;
}
else
{
lean_object* v_userName_3602_; lean_object* v_type_3603_; lean_object* v_value_3604_; uint8_t v_nondep_3605_; uint8_t v___y_3612_; 
v_userName_3602_ = lean_ctor_get(v_val_3598_, 2);
lean_inc(v_userName_3602_);
v_type_3603_ = lean_ctor_get(v_val_3598_, 3);
lean_inc_ref(v_type_3603_);
v_value_3604_ = lean_ctor_get(v_val_3598_, 4);
lean_inc_ref(v_value_3604_);
v_nondep_3605_ = lean_ctor_get_uint8(v_val_3598_, sizeof(void*)*5);
lean_dec_ref(v_val_3598_);
if (v_nondep_3605_ == 0)
{
v___y_3612_ = v_nondep_3605_;
goto v___jp_3611_;
}
else
{
if (v_generalizeNondepLet_3579_ == 0)
{
v___y_3612_ = v_generalizeNondepLet_3579_;
goto v___jp_3611_;
}
else
{
uint8_t v___x_3616_; 
lean_dec_ref(v_value_3604_);
v___x_3616_ = 0;
v_n_3587_ = v_userName_3602_;
v_ty_3588_ = v_type_3603_;
v_bi_3589_ = v___x_3616_;
goto v___jp_3586_;
}
}
v___jp_3606_:
{
lean_object* v_ty_3607_; lean_object* v_val_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v_ty_3607_ = lean_expr_abstract_range(v_type_3603_, v_n_3585_, v_xs_3576_);
lean_dec_ref(v_type_3603_);
v_val_3608_ = lean_expr_abstract_range(v_value_3604_, v_n_3585_, v_xs_3576_);
lean_dec_ref(v_value_3604_);
v___x_3609_ = l_Lean_Expr_letE___override(v_userName_3602_, v_ty_3607_, v_val_3608_, v_x_3581_, v_nondep_3605_);
v___x_3610_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3576_, v_lctx_3577_, v_usedLetOnly_3578_, v_generalizeNondepLet_3579_, v_n_3585_, v___x_3609_);
return v___x_3610_;
}
v___jp_3611_:
{
if (v_usedLetOnly_3578_ == 0)
{
goto v___jp_3606_;
}
else
{
if (v___y_3612_ == 0)
{
uint8_t v___x_3613_; 
v___x_3613_ = lean_expr_has_loose_bvar(v_x_3581_, v_zero_3582_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_dec_ref(v_value_3604_);
lean_dec_ref(v_type_3603_);
lean_dec(v_userName_3602_);
v___x_3614_ = lean_expr_lower_loose_bvars(v_x_3581_, v_one_3584_, v_one_3584_);
lean_dec_ref(v_x_3581_);
v___x_3615_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3576_, v_lctx_3577_, v_usedLetOnly_3578_, v_generalizeNondepLet_3579_, v_n_3585_, v___x_3614_);
return v___x_3615_;
}
else
{
goto v___jp_3606_;
}
}
else
{
goto v___jp_3606_;
}
}
}
}
}
v___jp_3586_:
{
lean_object* v_ty_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v_ty_3590_ = lean_expr_abstract_range(v_ty_3588_, v_n_3585_, v_xs_3576_);
lean_dec_ref(v_ty_3588_);
v___x_3591_ = l_Lean_mkForall(v_n_3587_, v_bi_3589_, v_ty_3590_, v_x_3581_);
v___x_3592_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3576_, v_lctx_3577_, v_usedLetOnly_3578_, v_generalizeNondepLet_3579_, v_n_3585_, v___x_3591_);
return v___x_3592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3617_, lean_object* v_lctx_3618_, lean_object* v_usedLetOnly_3619_, lean_object* v_generalizeNondepLet_3620_, lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
uint8_t v_usedLetOnly_boxed_3623_; uint8_t v_generalizeNondepLet_boxed_3624_; lean_object* v_res_3625_; 
v_usedLetOnly_boxed_3623_ = lean_unbox(v_usedLetOnly_3619_);
v_generalizeNondepLet_boxed_3624_ = lean_unbox(v_generalizeNondepLet_3620_);
v_res_3625_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3617_, v_lctx_3618_, v_usedLetOnly_boxed_3623_, v_generalizeNondepLet_boxed_3624_, v_x_3621_, v_x_3622_);
lean_dec(v_x_3621_);
lean_dec_ref(v_xs_3617_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3626_, lean_object* v_xs_3627_, lean_object* v_b_3628_, uint8_t v_usedLetOnly_3629_, uint8_t v_generalizeNondepLet_3630_){
_start:
{
lean_object* v_b_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v_b_3631_ = lean_expr_abstract(v_b_3628_, v_xs_3627_);
v___x_3632_ = lean_array_get_size(v_xs_3627_);
v___x_3633_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3627_, v_lctx_3626_, v_usedLetOnly_3629_, v_generalizeNondepLet_3630_, v___x_3632_, v_b_3631_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3634_, lean_object* v_xs_3635_, lean_object* v_b_3636_, lean_object* v_usedLetOnly_3637_, lean_object* v_generalizeNondepLet_3638_){
_start:
{
uint8_t v_usedLetOnly_boxed_3639_; uint8_t v_generalizeNondepLet_boxed_3640_; lean_object* v_res_3641_; 
v_usedLetOnly_boxed_3639_ = lean_unbox(v_usedLetOnly_3637_);
v_generalizeNondepLet_boxed_3640_ = lean_unbox(v_generalizeNondepLet_3638_);
v_res_3641_ = l_Lean_LocalContext_mkForall(v_lctx_3634_, v_xs_3635_, v_b_3636_, v_usedLetOnly_boxed_3639_, v_generalizeNondepLet_boxed_3640_);
lean_dec_ref(v_b_3636_);
lean_dec_ref(v_xs_3635_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3642_, lean_object* v_p_3643_, lean_object* v_d_3644_){
_start:
{
if (lean_obj_tag(v_d_3644_) == 0)
{
uint8_t v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
lean_dec(v_p_3643_);
v___x_3645_ = 0;
v___x_3646_ = lean_box(v___x_3645_);
v___x_3647_ = lean_apply_2(v_toPure_3642_, lean_box(0), v___x_3646_);
return v___x_3647_;
}
else
{
lean_object* v_val_3648_; lean_object* v___x_3649_; 
lean_dec(v_toPure_3642_);
v_val_3648_ = lean_ctor_get(v_d_3644_, 0);
lean_inc(v_val_3648_);
lean_dec_ref(v_d_3644_);
v___x_3649_ = lean_apply_1(v_p_3643_, v_val_3648_);
return v___x_3649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3650_, lean_object* v_lctx_3651_, lean_object* v_p_3652_){
_start:
{
lean_object* v_toApplicative_3653_; lean_object* v_decls_3654_; lean_object* v_toPure_3655_; lean_object* v___f_3656_; lean_object* v___x_3657_; 
v_toApplicative_3653_ = lean_ctor_get(v_inst_3650_, 0);
v_decls_3654_ = lean_ctor_get(v_lctx_3651_, 1);
lean_inc_ref(v_decls_3654_);
lean_dec_ref(v_lctx_3651_);
v_toPure_3655_ = lean_ctor_get(v_toApplicative_3653_, 1);
lean_inc(v_toPure_3655_);
v___f_3656_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3656_, 0, v_toPure_3655_);
lean_closure_set(v___f_3656_, 1, v_p_3652_);
v___x_3657_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3650_, v_decls_3654_, v___f_3656_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3658_, lean_object* v_inst_3659_, lean_object* v_lctx_3660_, lean_object* v_p_3661_){
_start:
{
lean_object* v_toApplicative_3662_; lean_object* v_decls_3663_; lean_object* v_toPure_3664_; lean_object* v___f_3665_; lean_object* v___x_3666_; 
v_toApplicative_3662_ = lean_ctor_get(v_inst_3659_, 0);
v_decls_3663_ = lean_ctor_get(v_lctx_3660_, 1);
lean_inc_ref(v_decls_3663_);
lean_dec_ref(v_lctx_3660_);
v_toPure_3664_ = lean_ctor_get(v_toApplicative_3662_, 1);
lean_inc(v_toPure_3664_);
v___f_3665_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3665_, 0, v_toPure_3664_);
lean_closure_set(v___f_3665_, 1, v_p_3661_);
v___x_3666_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3659_, v_decls_3663_, v___f_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3667_, uint8_t v_b_3668_){
_start:
{
if (v_b_3668_ == 0)
{
uint8_t v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = 1;
v___x_3670_ = lean_box(v___x_3669_);
v___x_3671_ = lean_apply_2(v_toPure_3667_, lean_box(0), v___x_3670_);
return v___x_3671_;
}
else
{
uint8_t v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = 0;
v___x_3673_ = lean_box(v___x_3672_);
v___x_3674_ = lean_apply_2(v_toPure_3667_, lean_box(0), v___x_3673_);
return v___x_3674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3675_, lean_object* v_b_3676_){
_start:
{
uint8_t v_b_boxed_3677_; lean_object* v_res_3678_; 
v_b_boxed_3677_ = lean_unbox(v_b_3676_);
v_res_3678_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3675_, v_b_boxed_3677_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3679_, lean_object* v_toBind_3680_, lean_object* v___f_3681_, lean_object* v_p_3682_, lean_object* v_v_3683_){
_start:
{
if (lean_obj_tag(v_v_3683_) == 0)
{
uint8_t v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
lean_dec(v_p_3682_);
v___x_3684_ = 1;
v___x_3685_ = lean_box(v___x_3684_);
v___x_3686_ = lean_apply_2(v_toPure_3679_, lean_box(0), v___x_3685_);
v___x_3687_ = lean_apply_4(v_toBind_3680_, lean_box(0), lean_box(0), v___x_3686_, v___f_3681_);
return v___x_3687_;
}
else
{
lean_object* v_val_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_dec(v_toPure_3679_);
v_val_3688_ = lean_ctor_get(v_v_3683_, 0);
lean_inc(v_val_3688_);
lean_dec_ref(v_v_3683_);
v___x_3689_ = lean_apply_1(v_p_3682_, v_val_3688_);
v___x_3690_ = lean_apply_4(v_toBind_3680_, lean_box(0), lean_box(0), v___x_3689_, v___f_3681_);
return v___x_3690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3691_, lean_object* v_lctx_3692_, lean_object* v_p_3693_){
_start:
{
lean_object* v_toApplicative_3694_; lean_object* v_decls_3695_; lean_object* v_toBind_3696_; lean_object* v_toPure_3697_; lean_object* v___f_3698_; lean_object* v___f_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v_toApplicative_3694_ = lean_ctor_get(v_inst_3691_, 0);
v_decls_3695_ = lean_ctor_get(v_lctx_3692_, 1);
lean_inc_ref(v_decls_3695_);
lean_dec_ref(v_lctx_3692_);
v_toBind_3696_ = lean_ctor_get(v_inst_3691_, 1);
lean_inc_n(v_toBind_3696_, 2);
v_toPure_3697_ = lean_ctor_get(v_toApplicative_3694_, 1);
lean_inc_n(v_toPure_3697_, 2);
v___f_3698_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3698_, 0, v_toPure_3697_);
lean_inc_ref(v___f_3698_);
v___f_3699_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3699_, 0, v_toPure_3697_);
lean_closure_set(v___f_3699_, 1, v_toBind_3696_);
lean_closure_set(v___f_3699_, 2, v___f_3698_);
lean_closure_set(v___f_3699_, 3, v_p_3693_);
v___x_3700_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3691_, v_decls_3695_, v___f_3699_);
v___x_3701_ = lean_apply_4(v_toBind_3696_, lean_box(0), lean_box(0), v___x_3700_, v___f_3698_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3702_, lean_object* v_inst_3703_, lean_object* v_lctx_3704_, lean_object* v_p_3705_){
_start:
{
lean_object* v_toApplicative_3706_; lean_object* v_decls_3707_; lean_object* v_toBind_3708_; lean_object* v_toPure_3709_; lean_object* v___f_3710_; lean_object* v___f_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_toApplicative_3706_ = lean_ctor_get(v_inst_3703_, 0);
v_decls_3707_ = lean_ctor_get(v_lctx_3704_, 1);
lean_inc_ref(v_decls_3707_);
lean_dec_ref(v_lctx_3704_);
v_toBind_3708_ = lean_ctor_get(v_inst_3703_, 1);
lean_inc_n(v_toBind_3708_, 2);
v_toPure_3709_ = lean_ctor_get(v_toApplicative_3706_, 1);
lean_inc_n(v_toPure_3709_, 2);
v___f_3710_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3710_, 0, v_toPure_3709_);
lean_inc_ref(v___f_3710_);
v___f_3711_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3711_, 0, v_toPure_3709_);
lean_closure_set(v___f_3711_, 1, v_toBind_3708_);
lean_closure_set(v___f_3711_, 2, v___f_3710_);
lean_closure_set(v___f_3711_, 3, v_p_3705_);
v___x_3712_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3703_, v_decls_3707_, v___f_3711_);
v___x_3713_ = lean_apply_4(v_toBind_3708_, lean_box(0), lean_box(0), v___x_3712_, v___f_3710_);
return v___x_3713_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3714_, lean_object* v_d_3715_){
_start:
{
if (lean_obj_tag(v_d_3715_) == 0)
{
uint8_t v___x_3716_; 
lean_dec_ref(v_p_3714_);
v___x_3716_ = 0;
return v___x_3716_;
}
else
{
lean_object* v_val_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v_val_3717_ = lean_ctor_get(v_d_3715_, 0);
lean_inc(v_val_3717_);
lean_dec_ref(v_d_3715_);
v___x_3718_ = lean_apply_1(v_p_3714_, v_val_3717_);
v___x_3719_ = lean_unbox(v___x_3718_);
return v___x_3719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3720_, lean_object* v_d_3721_){
_start:
{
uint8_t v_res_3722_; lean_object* v_r_3723_; 
v_res_3722_ = l_Lean_LocalContext_any___lam__0(v_p_3720_, v_d_3721_);
v_r_3723_ = lean_box(v_res_3722_);
return v_r_3723_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3724_, lean_object* v_p_3725_){
_start:
{
lean_object* v___x_3726_; lean_object* v_decls_3727_; lean_object* v___f_3728_; lean_object* v___x_3729_; uint8_t v___x_3730_; 
v___x_3726_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3727_ = lean_ctor_get(v_lctx_3724_, 1);
lean_inc_ref(v_decls_3727_);
lean_dec_ref(v_lctx_3724_);
v___f_3728_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3728_, 0, v_p_3725_);
v___x_3729_ = l_Lean_PersistentArray_anyM___redArg(v___x_3726_, v_decls_3727_, v___f_3728_);
v___x_3730_ = lean_unbox(v___x_3729_);
lean_dec(v___x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3731_, lean_object* v_p_3732_){
_start:
{
uint8_t v_res_3733_; lean_object* v_r_3734_; 
v_res_3733_ = l_Lean_LocalContext_any(v_lctx_3731_, v_p_3732_);
v_r_3734_ = lean_box(v_res_3733_);
return v_r_3734_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3735_, lean_object* v_v_3736_){
_start:
{
if (lean_obj_tag(v_v_3736_) == 0)
{
uint8_t v___x_3737_; 
lean_dec_ref(v_p_3735_);
v___x_3737_ = 0;
return v___x_3737_;
}
else
{
lean_object* v_val_3738_; lean_object* v___x_3739_; uint8_t v___x_3740_; 
v_val_3738_ = lean_ctor_get(v_v_3736_, 0);
lean_inc(v_val_3738_);
lean_dec_ref(v_v_3736_);
v___x_3739_ = lean_apply_1(v_p_3735_, v_val_3738_);
v___x_3740_ = lean_unbox(v___x_3739_);
if (v___x_3740_ == 0)
{
uint8_t v___x_3741_; 
v___x_3741_ = 1;
return v___x_3741_;
}
else
{
uint8_t v___x_3742_; 
v___x_3742_ = 0;
return v___x_3742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3743_, lean_object* v_v_3744_){
_start:
{
uint8_t v_res_3745_; lean_object* v_r_3746_; 
v_res_3745_ = l_Lean_LocalContext_all___lam__0(v_p_3743_, v_v_3744_);
v_r_3746_ = lean_box(v_res_3745_);
return v_r_3746_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3747_, lean_object* v_p_3748_){
_start:
{
lean_object* v___x_3749_; lean_object* v_decls_3750_; lean_object* v___f_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
v___x_3749_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3750_ = lean_ctor_get(v_lctx_3747_, 1);
lean_inc_ref(v_decls_3750_);
lean_dec_ref(v_lctx_3747_);
v___f_3751_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3751_, 0, v_p_3748_);
v___x_3752_ = l_Lean_PersistentArray_anyM___redArg(v___x_3749_, v_decls_3750_, v___f_3751_);
v___x_3753_ = lean_unbox(v___x_3752_);
lean_dec(v___x_3752_);
if (v___x_3753_ == 0)
{
uint8_t v___x_3754_; 
v___x_3754_ = 1;
return v___x_3754_;
}
else
{
uint8_t v___x_3755_; 
v___x_3755_ = 0;
return v___x_3755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3756_, lean_object* v_p_3757_){
_start:
{
uint8_t v_res_3758_; lean_object* v_r_3759_; 
v_res_3758_ = l_Lean_LocalContext_all(v_lctx_3756_, v_p_3757_);
v_r_3759_ = lean_box(v_res_3758_);
return v_r_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3760_, lean_object* v_a_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_zero_3764_; uint8_t v_isZero_3765_; 
v_zero_3764_ = lean_unsigned_to_nat(0u);
v_isZero_3765_ = lean_nat_dec_eq(v_i_3760_, v_zero_3764_);
if (v_isZero_3765_ == 1)
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
lean_dec(v_i_3760_);
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v_a_3761_);
lean_ctor_set(v___x_3766_, 1, v___y_3762_);
v___x_3767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
lean_ctor_set(v___x_3767_, 1, v___y_3763_);
return v___x_3767_;
}
else
{
lean_object* v_decls_3768_; lean_object* v_size_3769_; lean_object* v_one_3770_; lean_object* v_n_3771_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3788_; lean_object* v___y_3789_; uint8_t v___y_3790_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3800_; lean_object* v___x_3804_; uint8_t v___x_3805_; 
v_decls_3768_ = lean_ctor_get(v_a_3761_, 1);
v_size_3769_ = lean_ctor_get(v_decls_3768_, 2);
v_one_3770_ = lean_unsigned_to_nat(1u);
v_n_3771_ = lean_nat_sub(v_i_3760_, v_one_3770_);
lean_dec(v_i_3760_);
v___x_3804_ = lean_box(0);
v___x_3805_ = lean_nat_dec_lt(v_n_3771_, v_size_3769_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; 
v___x_3806_ = l_outOfBounds___redArg(v___x_3804_);
v___y_3800_ = v___x_3806_;
goto v___jp_3799_;
}
else
{
lean_object* v___x_3807_; 
v___x_3807_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3804_, v_decls_3768_, v_n_3771_);
v___y_3800_ = v___x_3807_;
goto v___jp_3799_;
}
v___jp_3772_:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Lean_LocalContext_setUserName(v_a_3761_, v___y_3776_, v___y_3774_);
v_i_3760_ = v_n_3771_;
v_a_3761_ = v___x_3777_;
v___y_3762_ = v___y_3773_;
v___y_3763_ = v___y_3775_;
goto _start;
}
v___jp_3779_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v_fst_3784_; lean_object* v_snd_3785_; lean_object* v_fvarId_3786_; 
lean_inc(v___y_3781_);
v___x_3782_ = l_Lean_NameSet_insert(v___y_3762_, v___y_3781_);
v___x_3783_ = l_Lean_sanitizeName(v___y_3781_, v___y_3763_);
v_fst_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_fst_3784_);
v_snd_3785_ = lean_ctor_get(v___x_3783_, 1);
lean_inc(v_snd_3785_);
lean_dec_ref(v___x_3783_);
v_fvarId_3786_ = lean_ctor_get(v___y_3780_, 1);
lean_inc(v_fvarId_3786_);
lean_dec_ref(v___y_3780_);
v___y_3773_ = v___x_3782_;
v___y_3774_ = v_fst_3784_;
v___y_3775_ = v_snd_3785_;
v___y_3776_ = v_fvarId_3786_;
goto v___jp_3772_;
}
v___jp_3787_:
{
if (v___y_3790_ == 0)
{
lean_object* v___x_3791_; 
lean_dec_ref(v___y_3788_);
v___x_3791_ = l_Lean_NameSet_insert(v___y_3762_, v___y_3789_);
v_i_3760_ = v_n_3771_;
v___y_3762_ = v___x_3791_;
goto _start;
}
else
{
v___y_3780_ = v___y_3788_;
v___y_3781_ = v___y_3789_;
goto v___jp_3779_;
}
}
v___jp_3793_:
{
uint8_t v___x_3796_; 
v___x_3796_ = l_Lean_Name_hasMacroScopes(v___y_3795_);
if (v___x_3796_ == 0)
{
lean_object* v_userName_3797_; uint8_t v___x_3798_; 
v_userName_3797_ = lean_ctor_get(v___y_3794_, 2);
v___x_3798_ = l_Lean_NameSet_contains(v___y_3762_, v_userName_3797_);
v___y_3788_ = v___y_3794_;
v___y_3789_ = v___y_3795_;
v___y_3790_ = v___x_3798_;
goto v___jp_3787_;
}
else
{
v___y_3780_ = v___y_3794_;
v___y_3781_ = v___y_3795_;
goto v___jp_3779_;
}
}
v___jp_3799_:
{
if (lean_obj_tag(v___y_3800_) == 0)
{
v_i_3760_ = v_n_3771_;
goto _start;
}
else
{
lean_object* v_val_3802_; lean_object* v_userName_3803_; 
v_val_3802_ = lean_ctor_get(v___y_3800_, 0);
lean_inc(v_val_3802_);
lean_dec_ref(v___y_3800_);
v_userName_3803_ = lean_ctor_get(v_val_3802_, 2);
lean_inc(v_userName_3803_);
v___y_3794_ = v_val_3802_;
v___y_3795_ = v_userName_3803_;
goto v___jp_3793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3808_, lean_object* v_a_3809_){
_start:
{
lean_object* v_options_3810_; uint8_t v___x_3811_; 
v_options_3810_ = lean_ctor_get(v_a_3809_, 0);
v___x_3811_ = l_Lean_getSanitizeNames(v_options_3810_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; 
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v_lctx_3808_);
lean_ctor_set(v___x_3812_, 1, v_a_3809_);
return v___x_3812_;
}
else
{
lean_object* v_decls_3813_; lean_object* v_size_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v_fst_3817_; lean_object* v_snd_3818_; lean_object* v_fst_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
v_decls_3813_ = lean_ctor_get(v_lctx_3808_, 1);
v_size_3814_ = lean_ctor_get(v_decls_3813_, 2);
lean_inc(v_size_3814_);
v___x_3815_ = l_Lean_NameSet_empty;
v___x_3816_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3814_, v_lctx_3808_, v___x_3815_, v_a_3809_);
v_fst_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_fst_3817_);
v_snd_3818_ = lean_ctor_get(v___x_3816_, 1);
lean_inc(v_snd_3818_);
lean_dec_ref(v___x_3816_);
v_fst_3819_ = lean_ctor_get(v_fst_3817_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_fst_3817_);
if (v_isSharedCheck_3826_ == 0)
{
lean_object* v_unused_3827_; 
v_unused_3827_ = lean_ctor_get(v_fst_3817_, 1);
lean_dec(v_unused_3827_);
v___x_3821_ = v_fst_3817_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_fst_3819_);
lean_dec(v_fst_3817_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 1, v_snd_3818_);
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_fst_3819_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v_snd_3818_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3828_, lean_object* v_i_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3829_, v_a_3831_, v___y_3832_, v___y_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3835_, lean_object* v_i_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3835_, v_i_3836_, v_a_3837_, v_a_3838_, v___y_3839_, v___y_3840_);
lean_dec(v_n_3835_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3842_, lean_object* v_fvarId_3843_){
_start:
{
lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___x_3856_; 
lean_inc_ref(v_lctx_3842_);
v___x_3856_ = lean_local_ctx_find(v_lctx_3842_, v_fvarId_3843_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v___x_3857_; 
lean_dec_ref(v_lctx_3842_);
v___x_3857_ = lean_box(0);
return v___x_3857_;
}
else
{
lean_object* v_val_3858_; lean_object* v___y_3860_; lean_object* v_userName_3865_; 
v_val_3858_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_val_3858_);
lean_dec_ref(v___x_3856_);
v_userName_3865_ = lean_ctor_get(v_val_3858_, 2);
lean_inc(v_userName_3865_);
v___y_3860_ = v_userName_3865_;
goto v___jp_3859_;
v___jp_3859_:
{
lean_object* v___x_3861_; 
v___x_3861_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3842_, v___y_3860_);
lean_dec_ref(v_lctx_3842_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v___x_3862_; 
lean_dec(v___y_3860_);
lean_dec(v_val_3858_);
v___x_3862_ = lean_box(0);
return v___x_3862_;
}
else
{
lean_object* v_val_3863_; lean_object* v_fvarId_3864_; 
v_val_3863_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_val_3863_);
lean_dec_ref(v___x_3861_);
v_fvarId_3864_ = lean_ctor_get(v_val_3858_, 1);
lean_inc(v_fvarId_3864_);
lean_dec(v_val_3858_);
v___y_3852_ = v_val_3863_;
v___y_3853_ = v___y_3860_;
v___y_3854_ = v_fvarId_3864_;
goto v___jp_3851_;
}
}
}
v___jp_3844_:
{
uint8_t v___x_3848_; 
v___x_3848_ = l_Lean_instBEqFVarId_beq(v___y_3845_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec(v___y_3845_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; 
lean_dec(v___y_3846_);
v___x_3849_ = lean_box(0);
return v___x_3849_;
}
else
{
lean_object* v___x_3850_; 
v___x_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3850_, 0, v___y_3846_);
return v___x_3850_;
}
}
v___jp_3851_:
{
lean_object* v_fvarId_3855_; 
v_fvarId_3855_ = lean_ctor_get(v___y_3852_, 1);
lean_inc(v_fvarId_3855_);
lean_dec_ref(v___y_3852_);
v___y_3845_ = v___y_3854_;
v___y_3846_ = v___y_3853_;
v___y_3847_ = v_fvarId_3855_;
goto v___jp_3844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3866_, size_t v_i_3867_, lean_object* v_bs_3868_){
_start:
{
uint8_t v___x_3869_; 
v___x_3869_ = lean_usize_dec_lt(v_i_3867_, v_sz_3866_);
if (v___x_3869_ == 0)
{
return v_bs_3868_;
}
else
{
lean_object* v_v_3870_; lean_object* v_snd_3871_; lean_object* v___x_3872_; lean_object* v_bs_x27_3873_; size_t v___x_3874_; size_t v___x_3875_; lean_object* v___x_3876_; 
v_v_3870_ = lean_array_uget_borrowed(v_bs_3868_, v_i_3867_);
v_snd_3871_ = lean_ctor_get(v_v_3870_, 1);
lean_inc(v_snd_3871_);
v___x_3872_ = lean_unsigned_to_nat(0u);
v_bs_x27_3873_ = lean_array_uset(v_bs_3868_, v_i_3867_, v___x_3872_);
v___x_3874_ = ((size_t)1ULL);
v___x_3875_ = lean_usize_add(v_i_3867_, v___x_3874_);
v___x_3876_ = lean_array_uset(v_bs_x27_3873_, v_i_3867_, v_snd_3871_);
v_i_3867_ = v___x_3875_;
v_bs_3868_ = v___x_3876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3878_, lean_object* v_i_3879_, lean_object* v_bs_3880_){
_start:
{
size_t v_sz_boxed_3881_; size_t v_i_boxed_3882_; lean_object* v_res_3883_; 
v_sz_boxed_3881_ = lean_unbox_usize(v_sz_3878_);
lean_dec(v_sz_3878_);
v_i_boxed_3882_ = lean_unbox_usize(v_i_3879_);
lean_dec(v_i_3879_);
v_res_3883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3881_, v_i_boxed_3882_, v_bs_3880_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3884_, size_t v_sz_3885_, size_t v_i_3886_, lean_object* v_bs_3887_){
_start:
{
uint8_t v___x_3888_; 
v___x_3888_ = lean_usize_dec_lt(v_i_3886_, v_sz_3885_);
if (v___x_3888_ == 0)
{
return v_bs_3887_;
}
else
{
lean_object* v_fvarIdToDecl_3889_; lean_object* v_v_3890_; lean_object* v___x_3891_; lean_object* v_bs_x27_3892_; lean_object* v___y_3894_; lean_object* v___x_3899_; 
v_fvarIdToDecl_3889_ = lean_ctor_get(v_lctx_3884_, 0);
v_v_3890_ = lean_array_uget(v_bs_3887_, v_i_3886_);
v___x_3891_ = lean_unsigned_to_nat(0u);
v_bs_x27_3892_ = lean_array_uset(v_bs_3887_, v_i_3886_, v___x_3891_);
v___x_3899_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3889_, v_v_3890_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v___x_3900_; 
v___x_3900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3891_);
lean_ctor_set(v___x_3900_, 1, v_v_3890_);
v___y_3894_ = v___x_3900_;
goto v___jp_3893_;
}
else
{
lean_object* v_val_3901_; lean_object* v_index_3902_; lean_object* v___x_3903_; 
v_val_3901_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_val_3901_);
lean_dec_ref(v___x_3899_);
v_index_3902_ = lean_ctor_get(v_val_3901_, 0);
lean_inc(v_index_3902_);
lean_dec(v_val_3901_);
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v_index_3902_);
lean_ctor_set(v___x_3903_, 1, v_v_3890_);
v___y_3894_ = v___x_3903_;
goto v___jp_3893_;
}
v___jp_3893_:
{
size_t v___x_3895_; size_t v___x_3896_; lean_object* v___x_3897_; 
v___x_3895_ = ((size_t)1ULL);
v___x_3896_ = lean_usize_add(v_i_3886_, v___x_3895_);
v___x_3897_ = lean_array_uset(v_bs_x27_3892_, v_i_3886_, v___y_3894_);
v_i_3886_ = v___x_3896_;
v_bs_3887_ = v___x_3897_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3904_, lean_object* v_sz_3905_, lean_object* v_i_3906_, lean_object* v_bs_3907_){
_start:
{
size_t v_sz_boxed_3908_; size_t v_i_boxed_3909_; lean_object* v_res_3910_; 
v_sz_boxed_3908_ = lean_unbox_usize(v_sz_3905_);
lean_dec(v_sz_3905_);
v_i_boxed_3909_ = lean_unbox_usize(v_i_3906_);
lean_dec(v_i_3906_);
v_res_3910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3904_, v_sz_boxed_3908_, v_i_boxed_3909_, v_bs_3907_);
lean_dec_ref(v_lctx_3904_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object* v_hi_3911_, lean_object* v_pivot_3912_, lean_object* v_as_3913_, lean_object* v_i_3914_, lean_object* v_k_3915_){
_start:
{
uint8_t v___x_3916_; 
v___x_3916_ = lean_nat_dec_lt(v_k_3915_, v_hi_3911_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_dec(v_k_3915_);
v___x_3917_ = lean_array_fswap(v_as_3913_, v_i_3914_, v_hi_3911_);
v___x_3918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3918_, 0, v_i_3914_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
return v___x_3918_;
}
else
{
lean_object* v___x_3919_; lean_object* v_fst_3920_; lean_object* v_fst_3921_; uint8_t v___x_3922_; 
v___x_3919_ = lean_array_fget_borrowed(v_as_3913_, v_k_3915_);
v_fst_3920_ = lean_ctor_get(v___x_3919_, 0);
v_fst_3921_ = lean_ctor_get(v_pivot_3912_, 0);
v___x_3922_ = lean_nat_dec_lt(v_fst_3920_, v_fst_3921_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = lean_unsigned_to_nat(1u);
v___x_3924_ = lean_nat_add(v_k_3915_, v___x_3923_);
lean_dec(v_k_3915_);
v_k_3915_ = v___x_3924_;
goto _start;
}
else
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3926_ = lean_array_fswap(v_as_3913_, v_i_3914_, v_k_3915_);
v___x_3927_ = lean_unsigned_to_nat(1u);
v___x_3928_ = lean_nat_add(v_i_3914_, v___x_3927_);
lean_dec(v_i_3914_);
v___x_3929_ = lean_nat_add(v_k_3915_, v___x_3927_);
lean_dec(v_k_3915_);
v_as_3913_ = v___x_3926_;
v_i_3914_ = v___x_3928_;
v_k_3915_ = v___x_3929_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object* v_hi_3931_, lean_object* v_pivot_3932_, lean_object* v_as_3933_, lean_object* v_i_3934_, lean_object* v_k_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3931_, v_pivot_3932_, v_as_3933_, v_i_3934_, v_k_3935_);
lean_dec_ref(v_pivot_3932_);
lean_dec(v_hi_3931_);
return v_res_3936_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3937_, lean_object* v_i_3938_){
_start:
{
lean_object* v_fst_3939_; lean_object* v_fst_3940_; uint8_t v___x_3941_; 
v_fst_3939_ = lean_ctor_get(v_h_3937_, 0);
v_fst_3940_ = lean_ctor_get(v_i_3938_, 0);
v___x_3941_ = lean_nat_dec_lt(v_fst_3939_, v_fst_3940_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3942_, lean_object* v_i_3943_){
_start:
{
uint8_t v_res_3944_; lean_object* v_r_3945_; 
v_res_3944_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3942_, v_i_3943_);
lean_dec_ref(v_i_3943_);
lean_dec_ref(v_h_3942_);
v_r_3945_ = lean_box(v_res_3944_);
return v_r_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_n_3946_, lean_object* v_as_3947_, lean_object* v_lo_3948_, lean_object* v_hi_3949_){
_start:
{
lean_object* v___y_3951_; uint8_t v___x_3961_; 
v___x_3961_ = lean_nat_dec_lt(v_lo_3948_, v_hi_3949_);
if (v___x_3961_ == 0)
{
lean_dec(v_lo_3948_);
return v_as_3947_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v_mid_3964_; lean_object* v___y_3966_; lean_object* v___y_3972_; lean_object* v___x_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3962_ = lean_nat_add(v_lo_3948_, v_hi_3949_);
v___x_3963_ = lean_unsigned_to_nat(1u);
v_mid_3964_ = lean_nat_shiftr(v___x_3962_, v___x_3963_);
lean_dec(v___x_3962_);
v___x_3977_ = lean_array_fget_borrowed(v_as_3947_, v_mid_3964_);
v___x_3978_ = lean_array_fget_borrowed(v_as_3947_, v_lo_3948_);
v___x_3979_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3977_, v___x_3978_);
if (v___x_3979_ == 0)
{
v___y_3972_ = v_as_3947_;
goto v___jp_3971_;
}
else
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_array_fswap(v_as_3947_, v_lo_3948_, v_mid_3964_);
v___y_3972_ = v___x_3980_;
goto v___jp_3971_;
}
v___jp_3965_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; uint8_t v___x_3969_; 
v___x_3967_ = lean_array_fget_borrowed(v___y_3966_, v_mid_3964_);
v___x_3968_ = lean_array_fget_borrowed(v___y_3966_, v_hi_3949_);
v___x_3969_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3967_, v___x_3968_);
if (v___x_3969_ == 0)
{
lean_dec(v_mid_3964_);
v___y_3951_ = v___y_3966_;
goto v___jp_3950_;
}
else
{
lean_object* v___x_3970_; 
v___x_3970_ = lean_array_fswap(v___y_3966_, v_mid_3964_, v_hi_3949_);
lean_dec(v_mid_3964_);
v___y_3951_ = v___x_3970_;
goto v___jp_3950_;
}
}
v___jp_3971_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; uint8_t v___x_3975_; 
v___x_3973_ = lean_array_fget_borrowed(v___y_3972_, v_hi_3949_);
v___x_3974_ = lean_array_fget_borrowed(v___y_3972_, v_lo_3948_);
v___x_3975_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3973_, v___x_3974_);
if (v___x_3975_ == 0)
{
v___y_3966_ = v___y_3972_;
goto v___jp_3965_;
}
else
{
lean_object* v___x_3976_; 
v___x_3976_ = lean_array_fswap(v___y_3972_, v_lo_3948_, v_hi_3949_);
v___y_3966_ = v___x_3976_;
goto v___jp_3965_;
}
}
}
v___jp_3950_:
{
lean_object* v_pivot_3952_; lean_object* v___x_3953_; lean_object* v_fst_3954_; lean_object* v_snd_3955_; uint8_t v___x_3956_; 
v_pivot_3952_ = lean_array_fget(v___y_3951_, v_hi_3949_);
lean_inc_n(v_lo_3948_, 2);
v___x_3953_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3949_, v_pivot_3952_, v___y_3951_, v_lo_3948_, v_lo_3948_);
lean_dec(v_pivot_3952_);
v_fst_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_fst_3954_);
v_snd_3955_ = lean_ctor_get(v___x_3953_, 1);
lean_inc(v_snd_3955_);
lean_dec_ref(v___x_3953_);
v___x_3956_ = lean_nat_dec_le(v_hi_3949_, v_fst_3954_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3957_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3946_, v_snd_3955_, v_lo_3948_, v_fst_3954_);
v___x_3958_ = lean_unsigned_to_nat(1u);
v___x_3959_ = lean_nat_add(v_fst_3954_, v___x_3958_);
lean_dec(v_fst_3954_);
v_as_3947_ = v___x_3957_;
v_lo_3948_ = v___x_3959_;
goto _start;
}
else
{
lean_dec(v_fst_3954_);
lean_dec(v_lo_3948_);
return v_snd_3955_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_n_3981_, lean_object* v_as_3982_, lean_object* v_lo_3983_, lean_object* v_hi_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3981_, v_as_3982_, v_lo_3983_, v_hi_3984_);
lean_dec(v_hi_3984_);
lean_dec(v_n_3981_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3986_, lean_object* v_hyps_3987_){
_start:
{
lean_object* v___y_3989_; size_t v_sz_3993_; size_t v___x_3994_; lean_object* v_hyps_3995_; lean_object* v___x_3996_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___x_4001_; uint8_t v___x_4002_; 
v_sz_3993_ = lean_array_size(v_hyps_3987_);
v___x_3994_ = ((size_t)0ULL);
v_hyps_3995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3986_, v_sz_3993_, v___x_3994_, v_hyps_3987_);
v___x_3996_ = lean_array_get_size(v_hyps_3995_);
v___x_4001_ = lean_unsigned_to_nat(0u);
v___x_4002_ = lean_nat_dec_eq(v___x_3996_, v___x_4001_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___y_4006_; uint8_t v___x_4008_; 
v___x_4003_ = lean_unsigned_to_nat(1u);
v___x_4004_ = lean_nat_sub(v___x_3996_, v___x_4003_);
v___x_4008_ = lean_nat_dec_le(v___x_4001_, v___x_4004_);
if (v___x_4008_ == 0)
{
lean_inc(v___x_4004_);
v___y_4006_ = v___x_4004_;
goto v___jp_4005_;
}
else
{
v___y_4006_ = v___x_4001_;
goto v___jp_4005_;
}
v___jp_4005_:
{
uint8_t v___x_4007_; 
v___x_4007_ = lean_nat_dec_le(v___y_4006_, v___x_4004_);
if (v___x_4007_ == 0)
{
lean_dec(v___x_4004_);
lean_inc(v___y_4006_);
v___y_3998_ = v___y_4006_;
v___y_3999_ = v___y_4006_;
goto v___jp_3997_;
}
else
{
v___y_3998_ = v___y_4006_;
v___y_3999_ = v___x_4004_;
goto v___jp_3997_;
}
}
}
else
{
v___y_3989_ = v_hyps_3995_;
goto v___jp_3988_;
}
v___jp_3988_:
{
size_t v_sz_3990_; size_t v___x_3991_; lean_object* v___x_3992_; 
v_sz_3990_ = lean_array_size(v___y_3989_);
v___x_3991_ = ((size_t)0ULL);
v___x_3992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3990_, v___x_3991_, v___y_3989_);
return v___x_3992_;
}
v___jp_3997_:
{
lean_object* v___x_4000_; 
v___x_4000_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v___x_3996_, v_hyps_3995_, v___y_3998_, v___y_3999_);
lean_dec(v___y_3999_);
v___y_3989_ = v___x_4000_;
goto v___jp_3988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object* v_lctx_4009_, lean_object* v_hyps_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_4009_, v_hyps_4010_);
lean_dec_ref(v_lctx_4009_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_4012_, lean_object* v_as_4013_, lean_object* v_lo_4014_, lean_object* v_hi_4015_, lean_object* v_w_4016_, lean_object* v_hlo_4017_, lean_object* v_hhi_4018_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_4012_, v_as_4013_, v_lo_4014_, v_hi_4015_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_4020_, lean_object* v_as_4021_, lean_object* v_lo_4022_, lean_object* v_hi_4023_, lean_object* v_w_4024_, lean_object* v_hlo_4025_, lean_object* v_hhi_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_4020_, v_as_4021_, v_lo_4022_, v_hi_4023_, v_w_4024_, v_hlo_4025_, v_hhi_4026_);
lean_dec(v_hi_4023_);
lean_dec(v_n_4020_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object* v_n_4028_, lean_object* v_lo_4029_, lean_object* v_hi_4030_, lean_object* v_hhi_4031_, lean_object* v_pivot_4032_, lean_object* v_as_4033_, lean_object* v_i_4034_, lean_object* v_k_4035_, lean_object* v_ilo_4036_, lean_object* v_ik_4037_, lean_object* v_w_4038_){
_start:
{
lean_object* v___x_4039_; 
v___x_4039_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_4030_, v_pivot_4032_, v_as_4033_, v_i_4034_, v_k_4035_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object* v_n_4040_, lean_object* v_lo_4041_, lean_object* v_hi_4042_, lean_object* v_hhi_4043_, lean_object* v_pivot_4044_, lean_object* v_as_4045_, lean_object* v_i_4046_, lean_object* v_k_4047_, lean_object* v_ilo_4048_, lean_object* v_ik_4049_, lean_object* v_w_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(v_n_4040_, v_lo_4041_, v_hi_4042_, v_hhi_4043_, v_pivot_4044_, v_as_4045_, v_i_4046_, v_k_4047_, v_ilo_4048_, v_ik_4049_, v_w_4050_);
lean_dec_ref(v_pivot_4044_);
lean_dec(v_hi_4042_);
lean_dec(v_lo_4041_);
lean_dec(v_n_4040_);
return v_res_4051_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_4052_, lean_object* v_x_4053_){
_start:
{
if (lean_obj_tag(v_x_4053_) == 0)
{
uint8_t v___x_4054_; 
v___x_4054_ = 0;
return v___x_4054_;
}
else
{
lean_object* v_key_4055_; lean_object* v_tail_4056_; uint8_t v___x_4057_; 
v_key_4055_ = lean_ctor_get(v_x_4053_, 0);
v_tail_4056_ = lean_ctor_get(v_x_4053_, 2);
v___x_4057_ = lean_name_eq(v_key_4055_, v_a_4052_);
if (v___x_4057_ == 0)
{
v_x_4053_ = v_tail_4056_;
goto _start;
}
else
{
return v___x_4057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_4059_, lean_object* v_x_4060_){
_start:
{
uint8_t v_res_4061_; lean_object* v_r_4062_; 
v_res_4061_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4059_, v_x_4060_);
lean_dec(v_x_4060_);
lean_dec(v_a_4059_);
v_r_4062_ = lean_box(v_res_4061_);
return v_r_4062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_4063_, lean_object* v_x_4064_){
_start:
{
if (lean_obj_tag(v_x_4064_) == 0)
{
return v_x_4064_;
}
else
{
lean_object* v_key_4065_; lean_object* v_value_4066_; lean_object* v_tail_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4076_; 
v_key_4065_ = lean_ctor_get(v_x_4064_, 0);
v_value_4066_ = lean_ctor_get(v_x_4064_, 1);
v_tail_4067_ = lean_ctor_get(v_x_4064_, 2);
v_isSharedCheck_4076_ = !lean_is_exclusive(v_x_4064_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4069_ = v_x_4064_;
v_isShared_4070_ = v_isSharedCheck_4076_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_tail_4067_);
lean_inc(v_value_4066_);
lean_inc(v_key_4065_);
lean_dec(v_x_4064_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4076_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
uint8_t v___x_4071_; 
v___x_4071_ = lean_name_eq(v_key_4065_, v_a_4063_);
if (v___x_4071_ == 0)
{
lean_object* v___x_4072_; lean_object* v___x_4074_; 
v___x_4072_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4063_, v_tail_4067_);
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 2, v___x_4072_);
v___x_4074_ = v___x_4069_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_key_4065_);
lean_ctor_set(v_reuseFailAlloc_4075_, 1, v_value_4066_);
lean_ctor_set(v_reuseFailAlloc_4075_, 2, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
else
{
lean_del_object(v___x_4069_);
lean_dec(v_value_4066_);
lean_dec(v_key_4065_);
return v_tail_4067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_4077_, lean_object* v_x_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4077_, v_x_4078_);
lean_dec(v_a_4077_);
return v_res_4079_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4080_; uint64_t v___x_4081_; 
v___x_4080_ = lean_unsigned_to_nat(1723u);
v___x_4081_ = lean_uint64_of_nat(v___x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_size_4084_; lean_object* v_buckets_4085_; lean_object* v___x_4086_; uint64_t v___y_4088_; 
v_size_4084_ = lean_ctor_get(v_m_4082_, 0);
v_buckets_4085_ = lean_ctor_get(v_m_4082_, 1);
v___x_4086_ = lean_array_get_size(v_buckets_4085_);
if (lean_obj_tag(v_a_4083_) == 0)
{
uint64_t v___x_4117_; 
v___x_4117_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_4088_ = v___x_4117_;
goto v___jp_4087_;
}
else
{
uint64_t v_hash_4118_; 
v_hash_4118_ = lean_ctor_get_uint64(v_a_4083_, sizeof(void*)*2);
v___y_4088_ = v_hash_4118_;
goto v___jp_4087_;
}
v___jp_4087_:
{
uint64_t v___x_4089_; uint64_t v___x_4090_; uint64_t v_fold_4091_; uint64_t v___x_4092_; uint64_t v___x_4093_; uint64_t v___x_4094_; size_t v___x_4095_; size_t v___x_4096_; size_t v___x_4097_; size_t v___x_4098_; size_t v___x_4099_; lean_object* v_bkt_4100_; uint8_t v___x_4101_; 
v___x_4089_ = 32ULL;
v___x_4090_ = lean_uint64_shift_right(v___y_4088_, v___x_4089_);
v_fold_4091_ = lean_uint64_xor(v___y_4088_, v___x_4090_);
v___x_4092_ = 16ULL;
v___x_4093_ = lean_uint64_shift_right(v_fold_4091_, v___x_4092_);
v___x_4094_ = lean_uint64_xor(v_fold_4091_, v___x_4093_);
v___x_4095_ = lean_uint64_to_usize(v___x_4094_);
v___x_4096_ = lean_usize_of_nat(v___x_4086_);
v___x_4097_ = ((size_t)1ULL);
v___x_4098_ = lean_usize_sub(v___x_4096_, v___x_4097_);
v___x_4099_ = lean_usize_land(v___x_4095_, v___x_4098_);
v_bkt_4100_ = lean_array_uget_borrowed(v_buckets_4085_, v___x_4099_);
v___x_4101_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4083_, v_bkt_4100_);
if (v___x_4101_ == 0)
{
return v_m_4082_;
}
else
{
lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4114_; 
lean_inc(v_bkt_4100_);
lean_inc_ref(v_buckets_4085_);
lean_inc(v_size_4084_);
v_isSharedCheck_4114_ = !lean_is_exclusive(v_m_4082_);
if (v_isSharedCheck_4114_ == 0)
{
lean_object* v_unused_4115_; lean_object* v_unused_4116_; 
v_unused_4115_ = lean_ctor_get(v_m_4082_, 1);
lean_dec(v_unused_4115_);
v_unused_4116_ = lean_ctor_get(v_m_4082_, 0);
lean_dec(v_unused_4116_);
v___x_4103_ = v_m_4082_;
v_isShared_4104_ = v_isSharedCheck_4114_;
goto v_resetjp_4102_;
}
else
{
lean_dec(v_m_4082_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4114_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4105_; lean_object* v_buckets_x27_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4112_; 
v___x_4105_ = lean_box(0);
v_buckets_x27_4106_ = lean_array_uset(v_buckets_4085_, v___x_4099_, v___x_4105_);
v___x_4107_ = lean_unsigned_to_nat(1u);
v___x_4108_ = lean_nat_sub(v_size_4084_, v___x_4107_);
lean_dec(v_size_4084_);
v___x_4109_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4083_, v_bkt_4100_);
v___x_4110_ = lean_array_uset(v_buckets_x27_4106_, v___x_4099_, v___x_4109_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 1, v___x_4110_);
lean_ctor_set(v___x_4103_, 0, v___x_4108_);
v___x_4112_ = v___x_4103_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4108_);
lean_ctor_set(v_reuseFailAlloc_4113_, 1, v___x_4110_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4119_, lean_object* v_a_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4119_, v_a_4120_);
lean_dec(v_a_4120_);
return v_res_4121_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v_buckets_4124_; lean_object* v___x_4125_; uint64_t v___y_4127_; 
v_buckets_4124_ = lean_ctor_get(v_m_4122_, 1);
v___x_4125_ = lean_array_get_size(v_buckets_4124_);
if (lean_obj_tag(v_a_4123_) == 0)
{
uint64_t v___x_4141_; 
v___x_4141_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_4127_ = v___x_4141_;
goto v___jp_4126_;
}
else
{
uint64_t v_hash_4142_; 
v_hash_4142_ = lean_ctor_get_uint64(v_a_4123_, sizeof(void*)*2);
v___y_4127_ = v_hash_4142_;
goto v___jp_4126_;
}
v___jp_4126_:
{
uint64_t v___x_4128_; uint64_t v___x_4129_; uint64_t v_fold_4130_; uint64_t v___x_4131_; uint64_t v___x_4132_; uint64_t v___x_4133_; size_t v___x_4134_; size_t v___x_4135_; size_t v___x_4136_; size_t v___x_4137_; size_t v___x_4138_; lean_object* v___x_4139_; uint8_t v___x_4140_; 
v___x_4128_ = 32ULL;
v___x_4129_ = lean_uint64_shift_right(v___y_4127_, v___x_4128_);
v_fold_4130_ = lean_uint64_xor(v___y_4127_, v___x_4129_);
v___x_4131_ = 16ULL;
v___x_4132_ = lean_uint64_shift_right(v_fold_4130_, v___x_4131_);
v___x_4133_ = lean_uint64_xor(v_fold_4130_, v___x_4132_);
v___x_4134_ = lean_uint64_to_usize(v___x_4133_);
v___x_4135_ = lean_usize_of_nat(v___x_4125_);
v___x_4136_ = ((size_t)1ULL);
v___x_4137_ = lean_usize_sub(v___x_4135_, v___x_4136_);
v___x_4138_ = lean_usize_land(v___x_4134_, v___x_4137_);
v___x_4139_ = lean_array_uget_borrowed(v_buckets_4124_, v___x_4138_);
v___x_4140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4123_, v___x_4139_);
return v___x_4140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4143_, lean_object* v_a_4144_){
_start:
{
uint8_t v_res_4145_; lean_object* v_r_4146_; 
v_res_4145_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4143_, v_a_4144_);
lean_dec(v_a_4144_);
lean_dec_ref(v_m_4143_);
v_r_4146_ = lean_box(v_res_4145_);
return v_r_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4147_, lean_object* v_as_4148_, size_t v_i_4149_, size_t v_stop_4150_, lean_object* v_b_4151_){
_start:
{
uint8_t v___x_4152_; 
v___x_4152_ = lean_usize_dec_eq(v_i_4149_, v_stop_4150_);
if (v___x_4152_ == 0)
{
size_t v___x_4153_; size_t v___x_4154_; lean_object* v___x_4155_; 
v___x_4153_ = ((size_t)1ULL);
v___x_4154_ = lean_usize_sub(v_i_4149_, v___x_4153_);
v___x_4155_ = lean_array_uget(v_as_4148_, v___x_4154_);
if (lean_obj_tag(v___x_4155_) == 0)
{
v_i_4149_ = v___x_4154_;
goto _start;
}
else
{
lean_object* v_val_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4191_; 
v_val_4157_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4159_ = v___x_4155_;
v_isShared_4160_ = v_isSharedCheck_4191_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_val_4157_);
lean_dec(v___x_4155_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4191_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v_fst_4161_; lean_object* v_snd_4162_; lean_object* v___y_4164_; lean_object* v___y_4180_; lean_object* v_size_4186_; lean_object* v___x_4187_; uint8_t v___x_4188_; 
v_fst_4161_ = lean_ctor_get(v_b_4151_, 0);
v_snd_4162_ = lean_ctor_get(v_b_4151_, 1);
v_size_4186_ = lean_ctor_get(v_fst_4161_, 0);
v___x_4187_ = lean_unsigned_to_nat(0u);
v___x_4188_ = lean_nat_dec_eq(v_size_4186_, v___x_4187_);
if (v___x_4188_ == 0)
{
lean_object* v_index_4189_; 
v_index_4189_ = lean_ctor_get(v_val_4157_, 0);
lean_inc(v_index_4189_);
v___y_4180_ = v_index_4189_;
goto v___jp_4179_;
}
else
{
lean_object* v___x_4190_; 
lean_inc(v_snd_4162_);
lean_del_object(v___x_4159_);
lean_dec(v_val_4157_);
lean_dec_ref(v_b_4151_);
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v_snd_4162_);
return v___x_4190_;
}
v___jp_4163_:
{
uint8_t v___x_4165_; 
v___x_4165_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4161_, v___y_4164_);
if (v___x_4165_ == 0)
{
lean_dec(v___y_4164_);
lean_dec(v_val_4157_);
v_i_4149_ = v___x_4154_;
goto _start;
}
else
{
lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4176_; 
lean_inc(v_snd_4162_);
lean_inc(v_fst_4161_);
v_isSharedCheck_4176_ = !lean_is_exclusive(v_b_4151_);
if (v_isSharedCheck_4176_ == 0)
{
lean_object* v_unused_4177_; lean_object* v_unused_4178_; 
v_unused_4177_ = lean_ctor_get(v_b_4151_, 1);
lean_dec(v_unused_4177_);
v_unused_4178_ = lean_ctor_get(v_b_4151_, 0);
lean_dec(v_unused_4178_);
v___x_4168_ = v_b_4151_;
v_isShared_4169_ = v_isSharedCheck_4176_;
goto v_resetjp_4167_;
}
else
{
lean_dec(v_b_4151_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4176_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4173_; 
v___x_4170_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4161_, v___y_4164_);
lean_dec(v___y_4164_);
v___x_4171_ = lean_array_push(v_snd_4162_, v_val_4157_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 1, v___x_4171_);
lean_ctor_set(v___x_4168_, 0, v___x_4170_);
v___x_4173_ = v___x_4168_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4170_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
v_i_4149_ = v___x_4154_;
v_b_4151_ = v___x_4173_;
goto _start;
}
}
}
}
v___jp_4179_:
{
uint8_t v___x_4181_; 
v___x_4181_ = lean_nat_dec_lt(v___y_4180_, v_start_4147_);
lean_dec(v___y_4180_);
if (v___x_4181_ == 0)
{
lean_object* v_userName_4182_; 
lean_del_object(v___x_4159_);
v_userName_4182_ = lean_ctor_get(v_val_4157_, 2);
lean_inc(v_userName_4182_);
v___y_4164_ = v_userName_4182_;
goto v___jp_4163_;
}
else
{
lean_object* v___x_4184_; 
lean_inc(v_snd_4162_);
lean_dec(v_val_4157_);
lean_dec_ref(v_b_4151_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set_tag(v___x_4159_, 0);
lean_ctor_set(v___x_4159_, 0, v_snd_4162_);
v___x_4184_ = v___x_4159_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_snd_4162_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
}
else
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4192_, 0, v_b_4151_);
return v___x_4192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4193_, lean_object* v_as_4194_, lean_object* v_i_4195_, lean_object* v_stop_4196_, lean_object* v_b_4197_){
_start:
{
size_t v_i_boxed_4198_; size_t v_stop_boxed_4199_; lean_object* v_res_4200_; 
v_i_boxed_4198_ = lean_unbox_usize(v_i_4195_);
lean_dec(v_i_4195_);
v_stop_boxed_4199_ = lean_unbox_usize(v_stop_4196_);
lean_dec(v_stop_4196_);
v_res_4200_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4193_, v_as_4194_, v_i_boxed_4198_, v_stop_boxed_4199_, v_b_4197_);
lean_dec_ref(v_as_4194_);
lean_dec(v_start_4193_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4201_, lean_object* v_x_4202_, lean_object* v_x_4203_){
_start:
{
if (lean_obj_tag(v_x_4202_) == 0)
{
lean_object* v_cs_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4217_; 
v_cs_4204_ = lean_ctor_get(v_x_4202_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v_x_4202_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4206_ = v_x_4202_;
v_isShared_4207_ = v_isSharedCheck_4217_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_cs_4204_);
lean_dec(v_x_4202_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4217_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v___x_4208_ = lean_array_get_size(v_cs_4204_);
v___x_4209_ = lean_unsigned_to_nat(0u);
v___x_4210_ = lean_nat_dec_lt(v___x_4209_, v___x_4208_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4212_; 
lean_dec_ref(v_cs_4204_);
if (v_isShared_4207_ == 0)
{
lean_ctor_set_tag(v___x_4206_, 1);
lean_ctor_set(v___x_4206_, 0, v_x_4203_);
v___x_4212_ = v___x_4206_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_x_4203_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
else
{
size_t v___x_4214_; size_t v___x_4215_; lean_object* v___x_4216_; 
lean_del_object(v___x_4206_);
v___x_4214_ = lean_usize_of_nat(v___x_4208_);
v___x_4215_ = ((size_t)0ULL);
v___x_4216_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4201_, v_cs_4204_, v___x_4214_, v___x_4215_, v_x_4203_);
lean_dec_ref(v_cs_4204_);
return v___x_4216_;
}
}
}
else
{
lean_object* v_vs_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4231_; 
v_vs_4218_ = lean_ctor_get(v_x_4202_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v_x_4202_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4220_ = v_x_4202_;
v_isShared_4221_ = v_isSharedCheck_4231_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_vs_4218_);
lean_dec(v_x_4202_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4231_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; 
v___x_4222_ = lean_array_get_size(v_vs_4218_);
v___x_4223_ = lean_unsigned_to_nat(0u);
v___x_4224_ = lean_nat_dec_lt(v___x_4223_, v___x_4222_);
if (v___x_4224_ == 0)
{
lean_object* v___x_4226_; 
lean_dec_ref(v_vs_4218_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v_x_4203_);
v___x_4226_ = v___x_4220_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_x_4203_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
else
{
size_t v___x_4228_; size_t v___x_4229_; lean_object* v___x_4230_; 
lean_del_object(v___x_4220_);
v___x_4228_ = lean_usize_of_nat(v___x_4222_);
v___x_4229_ = ((size_t)0ULL);
v___x_4230_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4201_, v_vs_4218_, v___x_4228_, v___x_4229_, v_x_4203_);
lean_dec_ref(v_vs_4218_);
return v___x_4230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4232_, lean_object* v_as_4233_, size_t v_i_4234_, size_t v_stop_4235_, lean_object* v_b_4236_){
_start:
{
uint8_t v___x_4237_; 
v___x_4237_ = lean_usize_dec_eq(v_i_4234_, v_stop_4235_);
if (v___x_4237_ == 0)
{
size_t v___x_4238_; size_t v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4238_ = ((size_t)1ULL);
v___x_4239_ = lean_usize_sub(v_i_4234_, v___x_4238_);
v___x_4240_ = lean_array_uget_borrowed(v_as_4233_, v___x_4239_);
lean_inc(v___x_4240_);
v___x_4241_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4232_, v___x_4240_, v_b_4236_);
if (lean_obj_tag(v___x_4241_) == 0)
{
return v___x_4241_;
}
else
{
lean_object* v_a_4242_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref(v___x_4241_);
v_i_4234_ = v___x_4239_;
v_b_4236_ = v_a_4242_;
goto _start;
}
}
else
{
lean_object* v___x_4244_; 
v___x_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4244_, 0, v_b_4236_);
return v___x_4244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4245_, lean_object* v_as_4246_, lean_object* v_i_4247_, lean_object* v_stop_4248_, lean_object* v_b_4249_){
_start:
{
size_t v_i_boxed_4250_; size_t v_stop_boxed_4251_; lean_object* v_res_4252_; 
v_i_boxed_4250_ = lean_unbox_usize(v_i_4247_);
lean_dec(v_i_4247_);
v_stop_boxed_4251_ = lean_unbox_usize(v_stop_4248_);
lean_dec(v_stop_4248_);
v_res_4252_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4245_, v_as_4246_, v_i_boxed_4250_, v_stop_boxed_4251_, v_b_4249_);
lean_dec_ref(v_as_4246_);
lean_dec(v_start_4245_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4253_, lean_object* v_x_4254_, lean_object* v_x_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4253_, v_x_4254_, v_x_4255_);
lean_dec(v_start_4253_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4257_, lean_object* v_t_4258_, lean_object* v_init_4259_){
_start:
{
lean_object* v_root_4260_; lean_object* v_tail_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; uint8_t v___x_4264_; 
v_root_4260_ = lean_ctor_get(v_t_4258_, 0);
lean_inc_ref(v_root_4260_);
v_tail_4261_ = lean_ctor_get(v_t_4258_, 1);
lean_inc_ref(v_tail_4261_);
lean_dec_ref(v_t_4258_);
v___x_4262_ = lean_array_get_size(v_tail_4261_);
v___x_4263_ = lean_unsigned_to_nat(0u);
v___x_4264_ = lean_nat_dec_lt(v___x_4263_, v___x_4262_);
if (v___x_4264_ == 0)
{
lean_object* v___x_4265_; 
lean_dec_ref(v_tail_4261_);
v___x_4265_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4257_, v_root_4260_, v_init_4259_);
return v___x_4265_;
}
else
{
size_t v___x_4266_; size_t v___x_4267_; lean_object* v___x_4268_; 
v___x_4266_ = lean_usize_of_nat(v___x_4262_);
v___x_4267_ = ((size_t)0ULL);
v___x_4268_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4257_, v_tail_4261_, v___x_4266_, v___x_4267_, v_init_4259_);
lean_dec_ref(v_tail_4261_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_dec_ref(v_root_4260_);
return v___x_4268_;
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4270_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_a_4269_);
lean_dec_ref(v___x_4268_);
v___x_4270_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4257_, v_root_4260_, v_a_4269_);
return v___x_4270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4271_, lean_object* v_t_4272_, lean_object* v_init_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4271_, v_t_4272_, v_init_4273_);
lean_dec(v_start_4271_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4275_, lean_object* v_lctx_4276_, lean_object* v_init_4277_){
_start:
{
lean_object* v_decls_4278_; lean_object* v___x_4279_; 
v_decls_4278_ = lean_ctor_get(v_lctx_4276_, 1);
lean_inc_ref(v_decls_4278_);
lean_dec_ref(v_lctx_4276_);
v___x_4279_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4275_, v_decls_4278_, v_init_4277_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4280_, lean_object* v_lctx_4281_, lean_object* v_init_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4280_, v_lctx_4281_, v_init_4282_);
lean_dec(v_start_4280_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4286_, lean_object* v_userNames_4287_, lean_object* v_start_4288_){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4289_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4290_, 0, v_userNames_4287_);
lean_ctor_set(v___x_4290_, 1, v___x_4289_);
v___x_4291_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4288_, v_lctx_4286_, v___x_4290_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4293_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref(v___x_4291_);
v___x_4293_ = l_Array_reverse___redArg(v_a_4292_);
return v___x_4293_;
}
else
{
lean_object* v_a_4294_; lean_object* v_snd_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
v_a_4294_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4294_);
lean_dec_ref(v___x_4291_);
v_snd_4295_ = lean_ctor_get(v_a_4294_, 1);
lean_inc(v_snd_4295_);
lean_dec(v_a_4294_);
v___x_4296_ = l_Array_reverse___redArg(v_snd_4295_);
v___x_4297_ = l_Array_reverse___redArg(v___x_4296_);
return v___x_4297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4298_, lean_object* v_userNames_4299_, lean_object* v_start_4300_){
_start:
{
lean_object* v_res_4301_; 
v_res_4301_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4298_, v_userNames_4299_, v_start_4300_);
lean_dec(v_start_4300_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4302_, lean_object* v_lctx_4303_, lean_object* v_userNames_4304_, lean_object* v_start_4305_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4303_, v_userNames_4304_, v_start_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4307_, lean_object* v_lctx_4308_, lean_object* v_userNames_4309_, lean_object* v_start_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4307_, v_lctx_4308_, v_userNames_4309_, v_start_4310_);
lean_dec(v_start_4310_);
return v_res_4311_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4312_, lean_object* v_m_4313_, lean_object* v_a_4314_){
_start:
{
uint8_t v___x_4315_; 
v___x_4315_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4313_, v_a_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4316_, lean_object* v_m_4317_, lean_object* v_a_4318_){
_start:
{
uint8_t v_res_4319_; lean_object* v_r_4320_; 
v_res_4319_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4316_, v_m_4317_, v_a_4318_);
lean_dec(v_a_4318_);
lean_dec_ref(v_m_4317_);
v_r_4320_ = lean_box(v_res_4319_);
return v_r_4320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4321_, lean_object* v_m_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4322_, v_a_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4325_, lean_object* v_m_4326_, lean_object* v_a_4327_){
_start:
{
lean_object* v_res_4328_; 
v_res_4328_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4325_, v_m_4326_, v_a_4327_);
lean_dec(v_a_4327_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4329_, lean_object* v_start_4330_, lean_object* v_lctx_4331_, lean_object* v_init_4332_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4330_, v_lctx_4331_, v_init_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4334_, lean_object* v_start_4335_, lean_object* v_lctx_4336_, lean_object* v_init_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4334_, v_start_4335_, v_lctx_4336_, v_init_4337_);
lean_dec(v_start_4335_);
return v_res_4338_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4339_, lean_object* v_a_4340_, lean_object* v_x_4341_){
_start:
{
uint8_t v___x_4342_; 
v___x_4342_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4340_, v_x_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4343_, lean_object* v_a_4344_, lean_object* v_x_4345_){
_start:
{
uint8_t v_res_4346_; lean_object* v_r_4347_; 
v_res_4346_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4343_, v_a_4344_, v_x_4345_);
lean_dec(v_x_4345_);
lean_dec(v_a_4344_);
v_r_4347_ = lean_box(v_res_4346_);
return v_r_4347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4348_, lean_object* v_a_4349_, lean_object* v_x_4350_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4349_, v_x_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4352_, lean_object* v_a_4353_, lean_object* v_x_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4352_, v_a_4353_, v_x_4354_);
lean_dec(v_a_4353_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4356_, lean_object* v_start_4357_, lean_object* v_t_4358_, lean_object* v_init_4359_){
_start:
{
lean_object* v___x_4360_; 
v___x_4360_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4357_, v_t_4358_, v_init_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4361_, lean_object* v_start_4362_, lean_object* v_t_4363_, lean_object* v_init_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4361_, v_start_4362_, v_t_4363_, v_init_4364_);
lean_dec(v_start_4362_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4366_, lean_object* v_start_4367_, lean_object* v_x_4368_, lean_object* v_x_4369_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4367_, v_x_4368_, v_x_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4371_, lean_object* v_start_4372_, lean_object* v_x_4373_, lean_object* v_x_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4371_, v_start_4372_, v_x_4373_, v_x_4374_);
lean_dec(v_start_4372_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4376_, lean_object* v_start_4377_, lean_object* v_as_4378_, size_t v_i_4379_, size_t v_stop_4380_, lean_object* v_b_4381_){
_start:
{
lean_object* v___x_4382_; 
v___x_4382_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4377_, v_as_4378_, v_i_4379_, v_stop_4380_, v_b_4381_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4383_, lean_object* v_start_4384_, lean_object* v_as_4385_, lean_object* v_i_4386_, lean_object* v_stop_4387_, lean_object* v_b_4388_){
_start:
{
size_t v_i_boxed_4389_; size_t v_stop_boxed_4390_; lean_object* v_res_4391_; 
v_i_boxed_4389_ = lean_unbox_usize(v_i_4386_);
lean_dec(v_i_4386_);
v_stop_boxed_4390_ = lean_unbox_usize(v_stop_4387_);
lean_dec(v_stop_4387_);
v_res_4391_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4383_, v_start_4384_, v_as_4385_, v_i_boxed_4389_, v_stop_boxed_4390_, v_b_4388_);
lean_dec_ref(v_as_4385_);
lean_dec(v_start_4384_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4392_, lean_object* v_start_4393_, lean_object* v_as_4394_, size_t v_i_4395_, size_t v_stop_4396_, lean_object* v_b_4397_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4393_, v_as_4394_, v_i_4395_, v_stop_4396_, v_b_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4399_, lean_object* v_start_4400_, lean_object* v_as_4401_, lean_object* v_i_4402_, lean_object* v_stop_4403_, lean_object* v_b_4404_){
_start:
{
size_t v_i_boxed_4405_; size_t v_stop_boxed_4406_; lean_object* v_res_4407_; 
v_i_boxed_4405_ = lean_unbox_usize(v_i_4402_);
lean_dec(v_i_4402_);
v_stop_boxed_4406_ = lean_unbox_usize(v_stop_4403_);
lean_dec(v_stop_4403_);
v_res_4407_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4399_, v_start_4400_, v_as_4401_, v_i_boxed_4405_, v_stop_boxed_4406_, v_b_4404_);
lean_dec_ref(v_as_4401_);
lean_dec(v_start_4400_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4408_, lean_object* v_inst_4409_){
_start:
{
lean_object* v___x_4410_; 
v___x_4410_ = lean_apply_2(v_inst_4408_, lean_box(0), v_inst_4409_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4411_, lean_object* v_n_4412_, lean_object* v_inst_4413_, lean_object* v_inst_4414_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = lean_apply_2(v_inst_4413_, lean_box(0), v_inst_4414_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4416_, lean_object* v_d_x3f_4417_, lean_object* v_b_4418_){
_start:
{
if (lean_obj_tag(v_d_x3f_4417_) == 0)
{
lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4419_, 0, v_b_4418_);
v___x_4420_ = lean_apply_2(v_toPure_4416_, lean_box(0), v___x_4419_);
return v___x_4420_;
}
else
{
lean_object* v_val_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4436_; 
v_val_4421_ = lean_ctor_get(v_d_x3f_4417_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v_d_x3f_4417_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4423_ = v_d_x3f_4417_;
v_isShared_4424_ = v_isSharedCheck_4436_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_val_4421_);
lean_dec(v_d_x3f_4417_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4436_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
uint8_t v___x_4425_; 
v___x_4425_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4421_);
if (v___x_4425_ == 0)
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4429_; 
v___x_4426_ = l_Lean_LocalDecl_toExpr(v_val_4421_);
v___x_4427_ = lean_array_push(v_b_4418_, v___x_4426_);
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 0, v___x_4427_);
v___x_4429_ = v___x_4423_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4427_);
v___x_4429_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
lean_object* v___x_4430_; 
v___x_4430_ = lean_apply_2(v_toPure_4416_, lean_box(0), v___x_4429_);
return v___x_4430_;
}
}
else
{
lean_object* v___x_4433_; 
lean_dec(v_val_4421_);
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 0, v_b_4418_);
v___x_4433_ = v___x_4423_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_b_4418_);
v___x_4433_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
lean_object* v___x_4434_; 
v___x_4434_ = lean_apply_2(v_toPure_4416_, lean_box(0), v___x_4433_);
return v___x_4434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4437_, lean_object* v_____s_4438_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = lean_apply_2(v_toPure_4437_, lean_box(0), v_____s_4438_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4440_, lean_object* v_hs_4441_, lean_object* v___f_4442_, lean_object* v_toBind_4443_, lean_object* v___f_4444_, lean_object* v_____do__lift_4445_){
_start:
{
lean_object* v_decls_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v_decls_4446_ = lean_ctor_get(v_____do__lift_4445_, 1);
v___x_4447_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4440_, v_decls_4446_, v_hs_4441_, v___f_4442_);
v___x_4448_ = lean_apply_4(v_toBind_4443_, lean_box(0), lean_box(0), v___x_4447_, v___f_4444_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object* v_inst_4449_, lean_object* v_hs_4450_, lean_object* v___f_4451_, lean_object* v_toBind_4452_, lean_object* v___f_4453_, lean_object* v_____do__lift_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Lean_getLocalHyps___redArg___lam__2(v_inst_4449_, v_hs_4450_, v___f_4451_, v_toBind_4452_, v___f_4453_, v_____do__lift_4454_);
lean_dec_ref(v_____do__lift_4454_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4458_, lean_object* v_inst_4459_){
_start:
{
lean_object* v_toApplicative_4460_; lean_object* v_toBind_4461_; lean_object* v_toPure_4462_; lean_object* v_hs_4463_; lean_object* v___f_4464_; lean_object* v___f_4465_; lean_object* v___f_4466_; lean_object* v___x_4467_; 
v_toApplicative_4460_ = lean_ctor_get(v_inst_4458_, 0);
v_toBind_4461_ = lean_ctor_get(v_inst_4458_, 1);
lean_inc_n(v_toBind_4461_, 2);
v_toPure_4462_ = lean_ctor_get(v_toApplicative_4460_, 1);
v_hs_4463_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4462_, 2);
v___f_4464_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4464_, 0, v_toPure_4462_);
v___f_4465_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4465_, 0, v_toPure_4462_);
v___f_4466_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_4466_, 0, v_inst_4458_);
lean_closure_set(v___f_4466_, 1, v_hs_4463_);
lean_closure_set(v___f_4466_, 2, v___f_4464_);
lean_closure_set(v___f_4466_, 3, v_toBind_4461_);
lean_closure_set(v___f_4466_, 4, v___f_4465_);
v___x_4467_ = lean_apply_4(v_toBind_4461_, lean_box(0), lean_box(0), v_inst_4459_, v___f_4466_);
return v___x_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4468_, lean_object* v_inst_4469_, lean_object* v_inst_4470_){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = l_Lean_getLocalHyps___redArg(v_inst_4469_, v_inst_4470_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4472_, lean_object* v_e_4473_, lean_object* v_d_4474_){
_start:
{
lean_object* v___y_4476_; lean_object* v_fvarId_4508_; 
v_fvarId_4508_ = lean_ctor_get(v_d_4474_, 1);
lean_inc(v_fvarId_4508_);
v___y_4476_ = v_fvarId_4508_;
goto v___jp_4475_;
v___jp_4475_:
{
uint8_t v___x_4477_; 
v___x_4477_ = l_Lean_instBEqFVarId_beq(v___y_4476_, v_fvarId_4472_);
lean_dec(v___y_4476_);
if (v___x_4477_ == 0)
{
if (lean_obj_tag(v_d_4474_) == 0)
{
lean_object* v_index_4478_; lean_object* v_fvarId_4479_; lean_object* v_userName_4480_; lean_object* v_type_4481_; uint8_t v_bi_4482_; uint8_t v_kind_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4491_; 
v_index_4478_ = lean_ctor_get(v_d_4474_, 0);
v_fvarId_4479_ = lean_ctor_get(v_d_4474_, 1);
v_userName_4480_ = lean_ctor_get(v_d_4474_, 2);
v_type_4481_ = lean_ctor_get(v_d_4474_, 3);
v_bi_4482_ = lean_ctor_get_uint8(v_d_4474_, sizeof(void*)*4);
v_kind_4483_ = lean_ctor_get_uint8(v_d_4474_, sizeof(void*)*4 + 1);
v_isSharedCheck_4491_ = !lean_is_exclusive(v_d_4474_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4485_ = v_d_4474_;
v_isShared_4486_ = v_isSharedCheck_4491_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_type_4481_);
lean_inc(v_userName_4480_);
lean_inc(v_fvarId_4479_);
lean_inc(v_index_4478_);
lean_dec(v_d_4474_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4491_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4487_ = l_Lean_Expr_replaceFVarId(v_type_4481_, v_fvarId_4472_, v_e_4473_);
lean_dec_ref(v_type_4481_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 3, v___x_4487_);
v___x_4489_ = v___x_4485_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_index_4478_);
lean_ctor_set(v_reuseFailAlloc_4490_, 1, v_fvarId_4479_);
lean_ctor_set(v_reuseFailAlloc_4490_, 2, v_userName_4480_);
lean_ctor_set(v_reuseFailAlloc_4490_, 3, v___x_4487_);
lean_ctor_set_uint8(v_reuseFailAlloc_4490_, sizeof(void*)*4, v_bi_4482_);
lean_ctor_set_uint8(v_reuseFailAlloc_4490_, sizeof(void*)*4 + 1, v_kind_4483_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
else
{
lean_object* v_index_4492_; lean_object* v_fvarId_4493_; lean_object* v_userName_4494_; lean_object* v_type_4495_; lean_object* v_value_4496_; uint8_t v_nondep_4497_; uint8_t v_kind_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4507_; 
v_index_4492_ = lean_ctor_get(v_d_4474_, 0);
v_fvarId_4493_ = lean_ctor_get(v_d_4474_, 1);
v_userName_4494_ = lean_ctor_get(v_d_4474_, 2);
v_type_4495_ = lean_ctor_get(v_d_4474_, 3);
v_value_4496_ = lean_ctor_get(v_d_4474_, 4);
v_nondep_4497_ = lean_ctor_get_uint8(v_d_4474_, sizeof(void*)*5);
v_kind_4498_ = lean_ctor_get_uint8(v_d_4474_, sizeof(void*)*5 + 1);
v_isSharedCheck_4507_ = !lean_is_exclusive(v_d_4474_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4500_ = v_d_4474_;
v_isShared_4501_ = v_isSharedCheck_4507_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_value_4496_);
lean_inc(v_type_4495_);
lean_inc(v_userName_4494_);
lean_inc(v_fvarId_4493_);
lean_inc(v_index_4492_);
lean_dec(v_d_4474_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4507_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4505_; 
lean_inc(v_fvarId_4472_);
v___x_4502_ = l_Lean_Expr_replaceFVarId(v_type_4495_, v_fvarId_4472_, v_e_4473_);
lean_dec_ref(v_type_4495_);
v___x_4503_ = l_Lean_Expr_replaceFVarId(v_value_4496_, v_fvarId_4472_, v_e_4473_);
lean_dec_ref(v_value_4496_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 4, v___x_4503_);
lean_ctor_set(v___x_4500_, 3, v___x_4502_);
v___x_4505_ = v___x_4500_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_index_4492_);
lean_ctor_set(v_reuseFailAlloc_4506_, 1, v_fvarId_4493_);
lean_ctor_set(v_reuseFailAlloc_4506_, 2, v_userName_4494_);
lean_ctor_set(v_reuseFailAlloc_4506_, 3, v___x_4502_);
lean_ctor_set(v_reuseFailAlloc_4506_, 4, v___x_4503_);
lean_ctor_set_uint8(v_reuseFailAlloc_4506_, sizeof(void*)*5, v_nondep_4497_);
lean_ctor_set_uint8(v_reuseFailAlloc_4506_, sizeof(void*)*5 + 1, v_kind_4498_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
else
{
lean_dec(v_fvarId_4472_);
return v_d_4474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4509_, lean_object* v_e_4510_, lean_object* v_d_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4509_, v_e_4510_, v_d_4511_);
lean_dec_ref(v_e_4510_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4513_, lean_object* v_e_4514_, lean_object* v_x_4515_){
_start:
{
lean_object* v___x_4516_; 
v___x_4516_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4513_, v_e_4514_, v_x_4515_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4517_, lean_object* v_e_4518_, lean_object* v_x_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4517_, v_e_4518_, v_x_4519_);
lean_dec_ref(v_e_4518_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4521_, lean_object* v_e_4522_, size_t v_sz_4523_, size_t v_i_4524_, lean_object* v_bs_4525_){
_start:
{
uint8_t v___x_4526_; 
v___x_4526_ = lean_usize_dec_lt(v_i_4524_, v_sz_4523_);
if (v___x_4526_ == 0)
{
lean_dec(v_fvarId_4521_);
return v_bs_4525_;
}
else
{
lean_object* v_v_4527_; lean_object* v___x_4528_; lean_object* v_bs_x27_4529_; lean_object* v___y_4531_; 
v_v_4527_ = lean_array_uget(v_bs_4525_, v_i_4524_);
v___x_4528_ = lean_unsigned_to_nat(0u);
v_bs_x27_4529_ = lean_array_uset(v_bs_4525_, v_i_4524_, v___x_4528_);
if (lean_obj_tag(v_v_4527_) == 0)
{
v___y_4531_ = v_v_4527_;
goto v___jp_4530_;
}
else
{
lean_object* v_val_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4544_; 
v_val_4536_ = lean_ctor_get(v_v_4527_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v_v_4527_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4538_ = v_v_4527_;
v_isShared_4539_ = v_isSharedCheck_4544_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_val_4536_);
lean_dec(v_v_4527_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4544_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4540_; lean_object* v___x_4542_; 
lean_inc(v_fvarId_4521_);
v___x_4540_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4521_, v_e_4522_, v_val_4536_);
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 0, v___x_4540_);
v___x_4542_ = v___x_4538_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4540_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
v___y_4531_ = v___x_4542_;
goto v___jp_4530_;
}
}
}
v___jp_4530_:
{
size_t v___x_4532_; size_t v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = ((size_t)1ULL);
v___x_4533_ = lean_usize_add(v_i_4524_, v___x_4532_);
v___x_4534_ = lean_array_uset(v_bs_x27_4529_, v_i_4524_, v___y_4531_);
v_i_4524_ = v___x_4533_;
v_bs_4525_ = v___x_4534_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4545_, lean_object* v_e_4546_, lean_object* v_sz_4547_, lean_object* v_i_4548_, lean_object* v_bs_4549_){
_start:
{
size_t v_sz_boxed_4550_; size_t v_i_boxed_4551_; lean_object* v_res_4552_; 
v_sz_boxed_4550_ = lean_unbox_usize(v_sz_4547_);
lean_dec(v_sz_4547_);
v_i_boxed_4551_ = lean_unbox_usize(v_i_4548_);
lean_dec(v_i_4548_);
v_res_4552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4545_, v_e_4546_, v_sz_boxed_4550_, v_i_boxed_4551_, v_bs_4549_);
lean_dec_ref(v_e_4546_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4553_, lean_object* v_e_4554_, size_t v_sz_4555_, size_t v_i_4556_, lean_object* v_bs_4557_){
_start:
{
uint8_t v___x_4558_; 
v___x_4558_ = lean_usize_dec_lt(v_i_4556_, v_sz_4555_);
if (v___x_4558_ == 0)
{
lean_dec(v_fvarId_4553_);
return v_bs_4557_;
}
else
{
lean_object* v_v_4559_; lean_object* v___x_4560_; lean_object* v_bs_x27_4561_; lean_object* v___x_4562_; size_t v___x_4563_; size_t v___x_4564_; lean_object* v___x_4565_; 
v_v_4559_ = lean_array_uget(v_bs_4557_, v_i_4556_);
v___x_4560_ = lean_unsigned_to_nat(0u);
v_bs_x27_4561_ = lean_array_uset(v_bs_4557_, v_i_4556_, v___x_4560_);
lean_inc(v_fvarId_4553_);
v___x_4562_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4553_, v_e_4554_, v_v_4559_);
v___x_4563_ = ((size_t)1ULL);
v___x_4564_ = lean_usize_add(v_i_4556_, v___x_4563_);
v___x_4565_ = lean_array_uset(v_bs_x27_4561_, v_i_4556_, v___x_4562_);
v_i_4556_ = v___x_4564_;
v_bs_4557_ = v___x_4565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4567_, lean_object* v_e_4568_, lean_object* v_x_4569_){
_start:
{
if (lean_obj_tag(v_x_4569_) == 0)
{
lean_object* v_cs_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4580_; 
v_cs_4570_ = lean_ctor_get(v_x_4569_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v_x_4569_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4572_ = v_x_4569_;
v_isShared_4573_ = v_isSharedCheck_4580_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_cs_4570_);
lean_dec(v_x_4569_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4580_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
size_t v_sz_4574_; size_t v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4578_; 
v_sz_4574_ = lean_array_size(v_cs_4570_);
v___x_4575_ = ((size_t)0ULL);
v___x_4576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4567_, v_e_4568_, v_sz_4574_, v___x_4575_, v_cs_4570_);
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 0, v___x_4576_);
v___x_4578_ = v___x_4572_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v___x_4576_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
else
{
lean_object* v_vs_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4591_; 
v_vs_4581_ = lean_ctor_get(v_x_4569_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v_x_4569_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4583_ = v_x_4569_;
v_isShared_4584_ = v_isSharedCheck_4591_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_vs_4581_);
lean_dec(v_x_4569_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4591_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
size_t v_sz_4585_; size_t v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4589_; 
v_sz_4585_ = lean_array_size(v_vs_4581_);
v___x_4586_ = ((size_t)0ULL);
v___x_4587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4567_, v_e_4568_, v_sz_4585_, v___x_4586_, v_vs_4581_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4587_);
v___x_4589_ = v___x_4583_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4587_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4592_, lean_object* v_e_4593_, lean_object* v_x_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4592_, v_e_4593_, v_x_4594_);
lean_dec_ref(v_e_4593_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4596_, lean_object* v_e_4597_, lean_object* v_sz_4598_, lean_object* v_i_4599_, lean_object* v_bs_4600_){
_start:
{
size_t v_sz_boxed_4601_; size_t v_i_boxed_4602_; lean_object* v_res_4603_; 
v_sz_boxed_4601_ = lean_unbox_usize(v_sz_4598_);
lean_dec(v_sz_4598_);
v_i_boxed_4602_ = lean_unbox_usize(v_i_4599_);
lean_dec(v_i_4599_);
v_res_4603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4596_, v_e_4597_, v_sz_boxed_4601_, v_i_boxed_4602_, v_bs_4600_);
lean_dec_ref(v_e_4597_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4604_, lean_object* v_e_4605_, lean_object* v_t_4606_){
_start:
{
lean_object* v_root_4607_; lean_object* v_tail_4608_; lean_object* v_size_4609_; size_t v_shift_4610_; lean_object* v_tailOff_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4622_; 
v_root_4607_ = lean_ctor_get(v_t_4606_, 0);
v_tail_4608_ = lean_ctor_get(v_t_4606_, 1);
v_size_4609_ = lean_ctor_get(v_t_4606_, 2);
v_shift_4610_ = lean_ctor_get_usize(v_t_4606_, 4);
v_tailOff_4611_ = lean_ctor_get(v_t_4606_, 3);
v_isSharedCheck_4622_ = !lean_is_exclusive(v_t_4606_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4613_ = v_t_4606_;
v_isShared_4614_ = v_isSharedCheck_4622_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_tailOff_4611_);
lean_inc(v_size_4609_);
lean_inc(v_tail_4608_);
lean_inc(v_root_4607_);
lean_dec(v_t_4606_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4622_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4615_; size_t v_sz_4616_; size_t v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4620_; 
lean_inc(v_fvarId_4604_);
v___x_4615_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4604_, v_e_4605_, v_root_4607_);
v_sz_4616_ = lean_array_size(v_tail_4608_);
v___x_4617_ = ((size_t)0ULL);
v___x_4618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4604_, v_e_4605_, v_sz_4616_, v___x_4617_, v_tail_4608_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 1, v___x_4618_);
lean_ctor_set(v___x_4613_, 0, v___x_4615_);
v___x_4620_ = v___x_4613_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4615_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v___x_4618_);
lean_ctor_set(v_reuseFailAlloc_4621_, 2, v_size_4609_);
lean_ctor_set(v_reuseFailAlloc_4621_, 3, v_tailOff_4611_);
lean_ctor_set_usize(v_reuseFailAlloc_4621_, 4, v_shift_4610_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4623_, lean_object* v_e_4624_, lean_object* v_t_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4623_, v_e_4624_, v_t_4625_);
lean_dec_ref(v_e_4624_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4627_, lean_object* v_x_4628_){
_start:
{
lean_object* v___x_4629_; 
v___x_4629_ = lean_apply_1(v_f_4627_, v_x_4628_);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4630_, lean_object* v_as_4631_, lean_object* v_i_4632_, lean_object* v_acc_4633_){
_start:
{
lean_object* v___x_4634_; uint8_t v___x_4635_; 
v___x_4634_ = lean_array_get_size(v_as_4631_);
v___x_4635_ = lean_nat_dec_eq(v_i_4632_, v___x_4634_);
if (v___x_4635_ == 0)
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4636_ = lean_array_fget_borrowed(v_as_4631_, v_i_4632_);
lean_inc(v_f_4630_);
lean_inc(v___x_4636_);
v___x_4637_ = lean_apply_1(v_f_4630_, v___x_4636_);
v___x_4638_ = lean_unsigned_to_nat(1u);
v___x_4639_ = lean_nat_add(v_i_4632_, v___x_4638_);
lean_dec(v_i_4632_);
v___x_4640_ = lean_array_push(v_acc_4633_, v___x_4637_);
v_i_4632_ = v___x_4639_;
v_acc_4633_ = v___x_4640_;
goto _start;
}
else
{
lean_dec(v_i_4632_);
lean_dec(v_f_4630_);
return v_acc_4633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4642_, lean_object* v_as_4643_, lean_object* v_i_4644_, lean_object* v_acc_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4642_, v_as_4643_, v_i_4644_, v_acc_4645_);
lean_dec_ref(v_as_4643_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4647_, lean_object* v_as_4648_){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4649_ = lean_unsigned_to_nat(0u);
v___x_4650_ = lean_array_get_size(v_as_4648_);
v___x_4651_ = lean_mk_empty_array_with_capacity(v___x_4650_);
v___x_4652_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4647_, v_as_4648_, v___x_4649_, v___x_4651_);
return v___x_4652_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4653_, lean_object* v_as_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4653_, v_as_4654_);
lean_dec_ref(v_as_4654_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4656_, size_t v_sz_4657_, size_t v_i_4658_, lean_object* v_bs_4659_){
_start:
{
uint8_t v___x_4660_; 
v___x_4660_ = lean_usize_dec_lt(v_i_4658_, v_sz_4657_);
if (v___x_4660_ == 0)
{
lean_dec(v_f_4656_);
return v_bs_4659_;
}
else
{
lean_object* v_v_4661_; lean_object* v___x_4662_; lean_object* v_bs_x27_4663_; lean_object* v___y_4665_; 
v_v_4661_ = lean_array_uget(v_bs_4659_, v_i_4658_);
v___x_4662_ = lean_unsigned_to_nat(0u);
v_bs_x27_4663_ = lean_array_uset(v_bs_4659_, v_i_4658_, v___x_4662_);
switch(lean_obj_tag(v_v_4661_))
{
case 0:
{
lean_object* v_key_4670_; lean_object* v_val_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4679_; 
v_key_4670_ = lean_ctor_get(v_v_4661_, 0);
v_val_4671_ = lean_ctor_get(v_v_4661_, 1);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_v_4661_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4673_ = v_v_4661_;
v_isShared_4674_ = v_isSharedCheck_4679_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_val_4671_);
lean_inc(v_key_4670_);
lean_dec(v_v_4661_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4679_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; lean_object* v___x_4677_; 
lean_inc(v_f_4656_);
v___x_4675_ = lean_apply_1(v_f_4656_, v_val_4671_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 1, v___x_4675_);
v___x_4677_ = v___x_4673_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_key_4670_);
lean_ctor_set(v_reuseFailAlloc_4678_, 1, v___x_4675_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
v___y_4665_ = v___x_4677_;
goto v___jp_4664_;
}
}
}
case 1:
{
lean_object* v_node_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4688_; 
v_node_4680_ = lean_ctor_get(v_v_4661_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v_v_4661_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4682_ = v_v_4661_;
v_isShared_4683_ = v_isSharedCheck_4688_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_node_4680_);
lean_dec(v_v_4661_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4688_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4684_; lean_object* v___x_4686_; 
lean_inc(v_f_4656_);
v___x_4684_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4656_, v_node_4680_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 0, v___x_4684_);
v___x_4686_ = v___x_4682_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4684_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
v___y_4665_ = v___x_4686_;
goto v___jp_4664_;
}
}
}
default: 
{
lean_object* v___x_4689_; 
v___x_4689_ = lean_box(2);
v___y_4665_ = v___x_4689_;
goto v___jp_4664_;
}
}
v___jp_4664_:
{
size_t v___x_4666_; size_t v___x_4667_; lean_object* v___x_4668_; 
v___x_4666_ = ((size_t)1ULL);
v___x_4667_ = lean_usize_add(v_i_4658_, v___x_4666_);
v___x_4668_ = lean_array_uset(v_bs_x27_4663_, v_i_4658_, v___y_4665_);
v_i_4658_ = v___x_4667_;
v_bs_4659_ = v___x_4668_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4690_, lean_object* v_n_4691_){
_start:
{
if (lean_obj_tag(v_n_4691_) == 0)
{
lean_object* v_es_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4702_; 
v_es_4692_ = lean_ctor_get(v_n_4691_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v_n_4691_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4694_ = v_n_4691_;
v_isShared_4695_ = v_isSharedCheck_4702_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_es_4692_);
lean_dec(v_n_4691_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4702_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
size_t v_sz_4696_; size_t v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4700_; 
v_sz_4696_ = lean_array_size(v_es_4692_);
v___x_4697_ = ((size_t)0ULL);
v___x_4698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4690_, v_sz_4696_, v___x_4697_, v_es_4692_);
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 0, v___x_4698_);
v___x_4700_ = v___x_4694_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v___x_4698_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
else
{
lean_object* v_ks_4703_; lean_object* v_vs_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4712_; 
v_ks_4703_ = lean_ctor_get(v_n_4691_, 0);
v_vs_4704_ = lean_ctor_get(v_n_4691_, 1);
v_isSharedCheck_4712_ = !lean_is_exclusive(v_n_4691_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4706_ = v_n_4691_;
v_isShared_4707_ = v_isSharedCheck_4712_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_vs_4704_);
lean_inc(v_ks_4703_);
lean_dec(v_n_4691_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4712_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v_val_4708_; lean_object* v___x_4710_; 
v_val_4708_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4690_, v_vs_4704_);
lean_dec_ref(v_vs_4704_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 1, v_val_4708_);
v___x_4710_ = v___x_4706_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_ks_4703_);
lean_ctor_set(v_reuseFailAlloc_4711_, 1, v_val_4708_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4713_, lean_object* v_sz_4714_, lean_object* v_i_4715_, lean_object* v_bs_4716_){
_start:
{
size_t v_sz_boxed_4717_; size_t v_i_boxed_4718_; lean_object* v_res_4719_; 
v_sz_boxed_4717_ = lean_unbox_usize(v_sz_4714_);
lean_dec(v_sz_4714_);
v_i_boxed_4718_ = lean_unbox_usize(v_i_4715_);
lean_dec(v_i_4715_);
v_res_4719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4713_, v_sz_boxed_4717_, v_i_boxed_4718_, v_bs_4716_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4720_, lean_object* v_f_4721_){
_start:
{
lean_object* v___f_4722_; lean_object* v___x_4723_; 
v___f_4722_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4722_, 0, v_f_4721_);
v___x_4723_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4722_, v_pm_4720_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4724_, lean_object* v_e_4725_, lean_object* v_lctx_4726_){
_start:
{
lean_object* v_lctx_4727_; lean_object* v_fvarIdToDecl_4728_; lean_object* v_decls_4729_; lean_object* v_auxDeclToFullName_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4740_; 
lean_inc(v_fvarId_4724_);
v_lctx_4727_ = lean_local_ctx_erase(v_lctx_4726_, v_fvarId_4724_);
v_fvarIdToDecl_4728_ = lean_ctor_get(v_lctx_4727_, 0);
v_decls_4729_ = lean_ctor_get(v_lctx_4727_, 1);
v_auxDeclToFullName_4730_ = lean_ctor_get(v_lctx_4727_, 2);
v_isSharedCheck_4740_ = !lean_is_exclusive(v_lctx_4727_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4732_ = v_lctx_4727_;
v_isShared_4733_ = v_isSharedCheck_4740_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_auxDeclToFullName_4730_);
lean_inc(v_decls_4729_);
lean_inc(v_fvarIdToDecl_4728_);
lean_dec(v_lctx_4727_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4740_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___f_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4738_; 
lean_inc_ref(v_e_4725_);
lean_inc(v_fvarId_4724_);
v___f_4734_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4734_, 0, v_fvarId_4724_);
lean_closure_set(v___f_4734_, 1, v_e_4725_);
v___x_4735_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4728_, v___f_4734_);
v___x_4736_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4724_, v_e_4725_, v_decls_4729_);
lean_dec_ref(v_e_4725_);
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 1, v___x_4736_);
lean_ctor_set(v___x_4732_, 0, v___x_4735_);
v___x_4738_ = v___x_4732_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___x_4735_);
lean_ctor_set(v_reuseFailAlloc_4739_, 1, v___x_4736_);
lean_ctor_set(v_reuseFailAlloc_4739_, 2, v_auxDeclToFullName_4730_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4741_, lean_object* v_00_u03c3_4742_, lean_object* v_pm_4743_, lean_object* v_f_4744_){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4743_, v_f_4744_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4746_, lean_object* v_f_4747_){
_start:
{
lean_object* v___x_4748_; 
v___x_4748_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4747_, v_pm_4746_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4749_, lean_object* v_00_u03c3_4750_, lean_object* v_pm_4751_, lean_object* v_f_4752_){
_start:
{
lean_object* v___x_4753_; 
v___x_4753_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4752_, v_pm_4751_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4754_, lean_object* v_00_u03b2_4755_, lean_object* v_00_u03c3_4756_, lean_object* v_f_4757_, lean_object* v_n_4758_){
_start:
{
lean_object* v___x_4759_; 
v___x_4759_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4757_, v_n_4758_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4760_, lean_object* v_00_u03b2_4761_, lean_object* v_00_u03c3_4762_, lean_object* v_f_4763_, size_t v_sz_4764_, size_t v_i_4765_, lean_object* v_bs_4766_){
_start:
{
lean_object* v___x_4767_; 
v___x_4767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4763_, v_sz_4764_, v_i_4765_, v_bs_4766_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4768_, lean_object* v_00_u03b2_4769_, lean_object* v_00_u03c3_4770_, lean_object* v_f_4771_, lean_object* v_sz_4772_, lean_object* v_i_4773_, lean_object* v_bs_4774_){
_start:
{
size_t v_sz_boxed_4775_; size_t v_i_boxed_4776_; lean_object* v_res_4777_; 
v_sz_boxed_4775_ = lean_unbox_usize(v_sz_4772_);
lean_dec(v_sz_4772_);
v_i_boxed_4776_ = lean_unbox_usize(v_i_4773_);
lean_dec(v_i_4773_);
v_res_4777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4768_, v_00_u03b2_4769_, v_00_u03c3_4770_, v_f_4771_, v_sz_boxed_4775_, v_i_boxed_4776_, v_bs_4774_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4778_, lean_object* v_00_u03b2_4779_, lean_object* v_f_4780_, lean_object* v_as_4781_){
_start:
{
lean_object* v___x_4782_; 
v___x_4782_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4780_, v_as_4781_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4783_, lean_object* v_00_u03b2_4784_, lean_object* v_f_4785_, lean_object* v_as_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4783_, v_00_u03b2_4784_, v_f_4785_, v_as_4786_);
lean_dec_ref(v_as_4786_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4788_, lean_object* v_00_u03b2_4789_, lean_object* v_f_4790_, lean_object* v_as_4791_, lean_object* v_i_4792_, lean_object* v_acc_4793_, lean_object* v_hle_4794_){
_start:
{
lean_object* v___x_4795_; 
v___x_4795_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4790_, v_as_4791_, v_i_4792_, v_acc_4793_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4796_, lean_object* v_00_u03b2_4797_, lean_object* v_f_4798_, lean_object* v_as_4799_, lean_object* v_i_4800_, lean_object* v_acc_4801_, lean_object* v_hle_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4796_, v_00_u03b2_4797_, v_f_4798_, v_as_4799_, v_i_4800_, v_acc_4801_, v_hle_4802_);
lean_dec_ref(v_as_4799_);
return v_res_4803_;
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
