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
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0;
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
static lean_once_cell_t l_Lean_LocalContext_all___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_LocalContext_all___lam__0___closed__0;
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
lean_dec_ref_known(v_t_160_, 4);
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
lean_dec_ref_known(v_t_160_, 5);
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
lean_dec_ref_known(v_x_245_, 4);
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
uint8_t v_kind_363_; 
v_kind_363_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*4 + 1);
v___y_359_ = v_kind_363_;
goto v___jp_358_;
}
else
{
uint8_t v_kind_364_; 
v_kind_364_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*5 + 1);
v___y_359_ = v_kind_364_;
goto v___jp_358_;
}
v___jp_358_:
{
uint8_t v___x_360_; uint8_t v___x_361_; uint8_t v___x_362_; 
v___x_360_ = 0;
v___x_361_ = l_Lean_instDecidableEqLocalDeclKind(v___y_359_, v___x_360_);
v___x_362_ = lean_bool_not(v___x_361_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* v_d_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Lean_LocalDecl_isImplementationDetail(v_d_365_);
lean_dec_ref(v_d_365_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object* v_x_368_, uint8_t v_x_369_){
_start:
{
if (lean_obj_tag(v_x_368_) == 1)
{
uint8_t v_nondep_370_; 
v_nondep_370_ = lean_ctor_get_uint8(v_x_368_, sizeof(void*)*5);
if (v_nondep_370_ == 0)
{
lean_object* v_value_371_; lean_object* v___x_372_; 
v_value_371_ = lean_ctor_get(v_x_368_, 4);
lean_inc_ref(v_value_371_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v_value_371_);
return v___x_372_;
}
else
{
if (v_x_369_ == 1)
{
lean_object* v_value_373_; lean_object* v___x_374_; 
v_value_373_ = lean_ctor_get(v_x_368_, 4);
lean_inc_ref(v_value_373_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v_value_373_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(0);
return v___x_375_;
}
}
}
else
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
uint8_t v_x_57__boxed_379_; lean_object* v_res_380_; 
v_x_57__boxed_379_ = lean_unbox(v_x_378_);
v_res_380_ = l_Lean_LocalDecl_value_x3f(v_x_377_, v_x_57__boxed_379_);
lean_dec_ref(v_x_377_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_381_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = l_Lean_instInhabitedExpr;
v___x_383_ = lean_panic_fn_borrowed(v___x_382_, v_msg_381_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_387_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__2));
v___x_388_ = lean_unsigned_to_nat(54u);
v___x_389_ = lean_unsigned_to_nat(172u);
v___x_390_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_391_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_392_ = l_mkPanicMessageWithDecl(v___x_391_, v___x_390_, v___x_389_, v___x_388_, v___x_387_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__5(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_394_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__4));
v___x_395_ = lean_unsigned_to_nat(54u);
v___x_396_ = lean_unsigned_to_nat(175u);
v___x_397_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_398_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_399_ = l_mkPanicMessageWithDecl(v___x_398_, v___x_397_, v___x_396_, v___x_395_, v___x_394_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object* v_x_400_, uint8_t v_x_401_){
_start:
{
if (lean_obj_tag(v_x_400_) == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__3, &l_Lean_LocalDecl_value___closed__3_once, _init_l_Lean_LocalDecl_value___closed__3);
v___x_403_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_402_);
return v___x_403_;
}
else
{
uint8_t v_nondep_404_; 
v_nondep_404_ = lean_ctor_get_uint8(v_x_400_, sizeof(void*)*5);
if (v_nondep_404_ == 0)
{
lean_object* v_value_405_; 
v_value_405_ = lean_ctor_get(v_x_400_, 4);
lean_inc_ref(v_value_405_);
return v_value_405_;
}
else
{
if (v_x_401_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__5, &l_Lean_LocalDecl_value___closed__5_once, _init_l_Lean_LocalDecl_value___closed__5);
v___x_407_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_406_);
return v___x_407_;
}
else
{
lean_object* v_value_408_; 
v_value_408_ = lean_ctor_get(v_x_400_, 4);
lean_inc_ref(v_value_408_);
return v_value_408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
uint8_t v_x_143__boxed_411_; lean_object* v_res_412_; 
v_x_143__boxed_411_ = lean_unbox(v_x_410_);
v_res_412_ = l_Lean_LocalDecl_value(v_x_409_, v_x_143__boxed_411_);
lean_dec_ref(v_x_409_);
return v_res_412_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object* v_x_413_, uint8_t v_x_414_){
_start:
{
if (lean_obj_tag(v_x_413_) == 0)
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
else
{
uint8_t v_nondep_416_; uint8_t v___x_417_; 
v_nondep_416_ = lean_ctor_get_uint8(v_x_413_, sizeof(void*)*5);
v___x_417_ = lean_bool_not(v_nondep_416_);
if (v___x_417_ == 0)
{
return v_x_414_;
}
else
{
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
uint8_t v_x_57__boxed_420_; uint8_t v_res_421_; lean_object* v_r_422_; 
v_x_57__boxed_420_ = lean_unbox(v_x_419_);
v_res_421_ = l_Lean_LocalDecl_hasValue(v_x_418_, v_x_57__boxed_420_);
lean_dec_ref(v_x_418_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
if (lean_obj_tag(v_x_423_) == 1)
{
lean_object* v_index_425_; lean_object* v_fvarId_426_; lean_object* v_userName_427_; lean_object* v_type_428_; uint8_t v_nondep_429_; uint8_t v_kind_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_index_425_ = lean_ctor_get(v_x_423_, 0);
v_fvarId_426_ = lean_ctor_get(v_x_423_, 1);
v_userName_427_ = lean_ctor_get(v_x_423_, 2);
v_type_428_ = lean_ctor_get(v_x_423_, 3);
v_nondep_429_ = lean_ctor_get_uint8(v_x_423_, sizeof(void*)*5);
v_kind_430_ = lean_ctor_get_uint8(v_x_423_, sizeof(void*)*5 + 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_423_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v_x_423_, 4);
lean_dec(v_unused_438_);
v___x_432_ = v_x_423_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_type_428_);
lean_inc(v_userName_427_);
lean_inc(v_fvarId_426_);
lean_inc(v_index_425_);
lean_dec(v_x_423_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 4, v_x_424_);
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_index_425_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_fvarId_426_);
lean_ctor_set(v_reuseFailAlloc_436_, 2, v_userName_427_);
lean_ctor_set(v_reuseFailAlloc_436_, 3, v_type_428_);
lean_ctor_set(v_reuseFailAlloc_436_, 4, v_x_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*5, v_nondep_429_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*5 + 1, v_kind_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
lean_dec_ref(v_x_424_);
return v_x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object* v_x_439_, uint8_t v_x_440_){
_start:
{
if (lean_obj_tag(v_x_439_) == 1)
{
lean_object* v_index_441_; lean_object* v_fvarId_442_; lean_object* v_userName_443_; lean_object* v_type_444_; lean_object* v_value_445_; uint8_t v_kind_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_index_441_ = lean_ctor_get(v_x_439_, 0);
v_fvarId_442_ = lean_ctor_get(v_x_439_, 1);
v_userName_443_ = lean_ctor_get(v_x_439_, 2);
v_type_444_ = lean_ctor_get(v_x_439_, 3);
v_value_445_ = lean_ctor_get(v_x_439_, 4);
v_kind_446_ = lean_ctor_get_uint8(v_x_439_, sizeof(void*)*5 + 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_439_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v_x_439_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_value_445_);
lean_inc(v_type_444_);
lean_inc(v_userName_443_);
lean_inc(v_fvarId_442_);
lean_inc(v_index_441_);
lean_dec(v_x_439_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_index_441_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_fvarId_442_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_userName_443_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_type_444_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_value_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_452_, sizeof(void*)*5 + 1, v_kind_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*5, v_x_440_);
return v___x_451_;
}
}
}
else
{
return v_x_439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
uint8_t v_x_27__boxed_456_; lean_object* v_res_457_; 
v_x_27__boxed_456_ = lean_unbox(v_x_455_);
v_res_457_ = l_Lean_LocalDecl_setNondep(v_x_454_, v_x_27__boxed_456_);
return v_res_457_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_458_) == 1)
{
uint8_t v_nondep_459_; 
v_nondep_459_ = lean_ctor_get_uint8(v_x_458_, sizeof(void*)*5);
return v_nondep_459_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = 0;
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object* v_x_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Lean_LocalDecl_isNondep(v_x_461_);
lean_dec_ref(v_x_461_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
if (lean_obj_tag(v_x_464_) == 0)
{
lean_object* v_index_466_; lean_object* v_fvarId_467_; lean_object* v_type_468_; uint8_t v_bi_469_; uint8_t v_kind_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
v_index_466_ = lean_ctor_get(v_x_464_, 0);
v_fvarId_467_ = lean_ctor_get(v_x_464_, 1);
v_type_468_ = lean_ctor_get(v_x_464_, 3);
v_bi_469_ = lean_ctor_get_uint8(v_x_464_, sizeof(void*)*4);
v_kind_470_ = lean_ctor_get_uint8(v_x_464_, sizeof(void*)*4 + 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_464_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_x_464_, 2);
lean_dec(v_unused_478_);
v___x_472_ = v_x_464_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_type_468_);
lean_inc(v_fvarId_467_);
lean_inc(v_index_466_);
lean_dec(v_x_464_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 2, v_x_465_);
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_index_466_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_fvarId_467_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_x_465_);
lean_ctor_set(v_reuseFailAlloc_476_, 3, v_type_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_476_, sizeof(void*)*4, v_bi_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_476_, sizeof(void*)*4 + 1, v_kind_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
else
{
lean_object* v_index_479_; lean_object* v_fvarId_480_; lean_object* v_type_481_; lean_object* v_value_482_; uint8_t v_nondep_483_; uint8_t v_kind_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_index_479_ = lean_ctor_get(v_x_464_, 0);
v_fvarId_480_ = lean_ctor_get(v_x_464_, 1);
v_type_481_ = lean_ctor_get(v_x_464_, 3);
v_value_482_ = lean_ctor_get(v_x_464_, 4);
v_nondep_483_ = lean_ctor_get_uint8(v_x_464_, sizeof(void*)*5);
v_kind_484_ = lean_ctor_get_uint8(v_x_464_, sizeof(void*)*5 + 1);
v_isSharedCheck_491_ = !lean_is_exclusive(v_x_464_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; 
v_unused_492_ = lean_ctor_get(v_x_464_, 2);
lean_dec(v_unused_492_);
v___x_486_ = v_x_464_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_value_482_);
lean_inc(v_type_481_);
lean_inc(v_fvarId_480_);
lean_inc(v_index_479_);
lean_dec(v_x_464_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 2, v_x_465_);
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_index_479_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_fvarId_480_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_x_465_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v_type_481_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v_value_482_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*5, v_nondep_483_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*5 + 1, v_kind_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object* v_msg_493_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = l_Lean_instInhabitedLocalDecl_default;
v___x_495_ = lean_panic_fn_borrowed(v___x_494_, v_msg_493_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_498_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__1));
v___x_499_ = lean_unsigned_to_nat(38u);
v___x_500_ = lean_unsigned_to_nat(237u);
v___x_501_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__0));
v___x_502_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_503_ = l_mkPanicMessageWithDecl(v___x_502_, v___x_501_, v___x_500_, v___x_499_, v___x_498_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* v_x_504_, uint8_t v_x_505_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
lean_object* v_index_506_; lean_object* v_fvarId_507_; lean_object* v_userName_508_; lean_object* v_type_509_; uint8_t v_kind_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v_index_506_ = lean_ctor_get(v_x_504_, 0);
v_fvarId_507_ = lean_ctor_get(v_x_504_, 1);
v_userName_508_ = lean_ctor_get(v_x_504_, 2);
v_type_509_ = lean_ctor_get(v_x_504_, 3);
v_kind_510_ = lean_ctor_get_uint8(v_x_504_, sizeof(void*)*4 + 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v_x_504_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_type_509_);
lean_inc(v_userName_508_);
lean_inc(v_fvarId_507_);
lean_inc(v_index_506_);
lean_dec(v_x_504_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_index_506_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_fvarId_507_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_userName_508_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_type_509_);
lean_ctor_set_uint8(v_reuseFailAlloc_516_, sizeof(void*)*4 + 1, v_kind_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*4, v_x_505_);
return v___x_515_;
}
}
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec_ref_known(v_x_504_, 5);
v___x_518_ = lean_obj_once(&l_Lean_LocalDecl_setBinderInfo___closed__2, &l_Lean_LocalDecl_setBinderInfo___closed__2_once, _init_l_Lean_LocalDecl_setBinderInfo___closed__2);
v___x_519_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
uint8_t v_x_84__boxed_522_; lean_object* v_res_523_; 
v_x_84__boxed_522_ = lean_unbox(v_x_521_);
v_res_523_ = l_Lean_LocalDecl_setBinderInfo(v_x_520_, v_x_84__boxed_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* v_decl_524_){
_start:
{
lean_object* v_fvarId_525_; lean_object* v___x_526_; 
v_fvarId_525_ = lean_ctor_get(v_decl_524_, 1);
lean_inc(v_fvarId_525_);
lean_dec_ref(v_decl_524_);
v___x_526_ = l_Lean_mkFVar(v_fvarId_525_);
return v___x_526_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* v_x_527_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
lean_object* v_type_528_; uint8_t v___x_529_; 
v_type_528_ = lean_ctor_get(v_x_527_, 3);
v___x_529_ = l_Lean_Expr_hasExprMVar(v_type_528_);
return v___x_529_;
}
else
{
lean_object* v_type_530_; lean_object* v_value_531_; uint8_t v___x_532_; 
v_type_530_ = lean_ctor_get(v_x_527_, 3);
v_value_531_ = lean_ctor_get(v_x_527_, 4);
v___x_532_ = l_Lean_Expr_hasExprMVar(v_type_530_);
if (v___x_532_ == 0)
{
uint8_t v___x_533_; 
v___x_533_ = l_Lean_Expr_hasExprMVar(v_value_531_);
return v___x_533_;
}
else
{
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* v_x_534_){
_start:
{
uint8_t v_res_535_; lean_object* v_r_536_; 
v_res_535_ = l_Lean_LocalDecl_hasExprMVar(v_x_534_);
lean_dec_ref(v_x_534_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object* v_x_537_, uint8_t v_x_538_){
_start:
{
if (lean_obj_tag(v_x_537_) == 0)
{
lean_object* v_index_539_; lean_object* v_fvarId_540_; lean_object* v_userName_541_; lean_object* v_type_542_; uint8_t v_bi_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v_index_539_ = lean_ctor_get(v_x_537_, 0);
v_fvarId_540_ = lean_ctor_get(v_x_537_, 1);
v_userName_541_ = lean_ctor_get(v_x_537_, 2);
v_type_542_ = lean_ctor_get(v_x_537_, 3);
v_bi_543_ = lean_ctor_get_uint8(v_x_537_, sizeof(void*)*4);
v_isSharedCheck_550_ = !lean_is_exclusive(v_x_537_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v_x_537_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_type_542_);
lean_inc(v_userName_541_);
lean_inc(v_fvarId_540_);
lean_inc(v_index_539_);
lean_dec(v_x_537_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_index_539_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_fvarId_540_);
lean_ctor_set(v_reuseFailAlloc_549_, 2, v_userName_541_);
lean_ctor_set(v_reuseFailAlloc_549_, 3, v_type_542_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, sizeof(void*)*4, v_bi_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*4 + 1, v_x_538_);
return v___x_548_;
}
}
}
else
{
lean_object* v_index_551_; lean_object* v_fvarId_552_; lean_object* v_userName_553_; lean_object* v_type_554_; lean_object* v_value_555_; uint8_t v_nondep_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_index_551_ = lean_ctor_get(v_x_537_, 0);
v_fvarId_552_ = lean_ctor_get(v_x_537_, 1);
v_userName_553_ = lean_ctor_get(v_x_537_, 2);
v_type_554_ = lean_ctor_get(v_x_537_, 3);
v_value_555_ = lean_ctor_get(v_x_537_, 4);
v_nondep_556_ = lean_ctor_get_uint8(v_x_537_, sizeof(void*)*5);
v_isSharedCheck_563_ = !lean_is_exclusive(v_x_537_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v_x_537_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_value_555_);
lean_inc(v_type_554_);
lean_inc(v_userName_553_);
lean_inc(v_fvarId_552_);
lean_inc(v_index_551_);
lean_dec(v_x_537_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_index_551_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_fvarId_552_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_userName_553_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_type_554_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_value_555_);
lean_ctor_set_uint8(v_reuseFailAlloc_562_, sizeof(void*)*5, v_nondep_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*5 + 1, v_x_538_);
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
uint8_t v_x_31__boxed_566_; lean_object* v_res_567_; 
v_x_31__boxed_566_ = lean_unbox(v_x_565_);
v_res_567_ = l_Lean_LocalDecl_setKind(v_x_564_, v_x_31__boxed_566_);
return v_res_567_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__0(void){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_568_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__1(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__0, &l_Lean_instInhabitedLocalContext_default___closed__0_once, _init_l_Lean_instInhabitedLocalContext_default___closed__0);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__2(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_unsigned_to_nat(32u);
v___x_572_ = lean_mk_empty_array_with_capacity(v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
size_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_574_ = ((size_t)5ULL);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_unsigned_to_nat(32u);
v___x_577_ = lean_mk_empty_array_with_capacity(v___x_576_);
v___x_578_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_579_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
lean_ctor_set(v___x_579_, 2, v___x_575_);
lean_ctor_set(v___x_579_, 3, v___x_575_);
lean_ctor_set_usize(v___x_579_, 4, v___x_574_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__4(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_580_ = lean_box(1);
v___x_581_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
v___x_582_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
lean_ctor_set(v___x_583_, 2, v___x_580_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_instInhabitedLocalContext_default;
return v___x_585_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_unsigned_to_nat(32u);
v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
lean_dec_ref(v___x_588_);
v___x_589_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_unsigned_to_nat(32u);
v___x_591_ = lean_mk_empty_array_with_capacity(v___x_590_);
lean_dec_ref(v___x_591_);
v___x_592_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_592_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_593_){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_595_){
_start:
{
uint8_t v_res_596_; lean_object* v_r_597_; 
v_res_596_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_595_);
lean_dec_ref(v_x_595_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_598_, lean_object* v_x_599_){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_601_, lean_object* v_x_602_){
_start:
{
uint8_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_601_, v_x_602_);
lean_dec_ref(v_x_602_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object* v_lctx_605_){
_start:
{
lean_object* v_fvarIdToDecl_606_; uint8_t v___x_607_; 
v_fvarIdToDecl_606_ = lean_ctor_get(v_lctx_605_, 0);
lean_inc_ref(v_fvarIdToDecl_606_);
lean_dec_ref(v_lctx_605_);
v___x_607_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_606_);
lean_dec_ref(v_fvarIdToDecl_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_608_){
_start:
{
uint8_t v_res_609_; lean_object* v_r_610_; 
v_res_609_ = lean_local_ctx_is_empty(v_lctx_608_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
lean_object* v_ks_615_; lean_object* v_vs_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_640_; 
v_ks_615_ = lean_ctor_get(v_x_611_, 0);
v_vs_616_ = lean_ctor_get(v_x_611_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_611_);
if (v_isSharedCheck_640_ == 0)
{
v___x_618_ = v_x_611_;
v_isShared_619_ = v_isSharedCheck_640_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_vs_616_);
lean_inc(v_ks_615_);
lean_dec(v_x_611_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_640_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_array_get_size(v_ks_615_);
v___x_621_ = lean_nat_dec_lt(v_x_612_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
lean_dec(v_x_612_);
v___x_622_ = lean_array_push(v_ks_615_, v_x_613_);
v___x_623_ = lean_array_push(v_vs_616_, v_x_614_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_623_);
lean_ctor_set(v___x_618_, 0, v___x_622_);
v___x_625_ = v___x_618_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
else
{
lean_object* v_k_x27_627_; uint8_t v___x_628_; 
v_k_x27_627_ = lean_array_fget_borrowed(v_ks_615_, v_x_612_);
v___x_628_ = l_Lean_instBEqFVarId_beq(v_x_613_, v_k_x27_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_630_; 
if (v_isShared_619_ == 0)
{
v___x_630_ = v___x_618_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_ks_615_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_vs_616_);
v___x_630_ = v_reuseFailAlloc_634_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_add(v_x_612_, v___x_631_);
lean_dec(v_x_612_);
v_x_611_ = v___x_630_;
v_x_612_ = v___x_632_;
goto _start;
}
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_635_ = lean_array_fset(v_ks_615_, v_x_612_, v_x_613_);
v___x_636_ = lean_array_fset(v_vs_616_, v_x_612_, v_x_614_);
lean_dec(v_x_612_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_636_);
lean_ctor_set(v___x_618_, 0, v___x_635_);
v___x_638_ = v___x_618_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_641_, lean_object* v_k_642_, lean_object* v_v_643_){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_641_, v___x_644_, v_k_642_, v_v_643_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_647_, size_t v_x_648_, size_t v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
if (lean_obj_tag(v_x_647_) == 0)
{
lean_object* v_es_652_; size_t v___x_653_; size_t v___x_654_; lean_object* v_j_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_es_652_ = lean_ctor_get(v_x_647_, 0);
v___x_653_ = ((size_t)31ULL);
v___x_654_ = lean_usize_land(v_x_648_, v___x_653_);
v_j_655_ = lean_usize_to_nat(v___x_654_);
v___x_656_ = lean_array_get_size(v_es_652_);
v___x_657_ = lean_nat_dec_lt(v_j_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_dec(v_j_655_);
lean_dec(v_x_651_);
lean_dec(v_x_650_);
return v_x_647_;
}
else
{
lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_696_; 
lean_inc_ref(v_es_652_);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_647_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v_x_647_, 0);
lean_dec(v_unused_697_);
v___x_659_ = v_x_647_;
v_isShared_660_ = v_isSharedCheck_696_;
goto v_resetjp_658_;
}
else
{
lean_dec(v_x_647_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_696_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_v_661_; lean_object* v___x_662_; lean_object* v_xs_x27_663_; lean_object* v___y_665_; 
v_v_661_ = lean_array_fget(v_es_652_, v_j_655_);
v___x_662_ = lean_box(0);
v_xs_x27_663_ = lean_array_fset(v_es_652_, v_j_655_, v___x_662_);
switch(lean_obj_tag(v_v_661_))
{
case 0:
{
lean_object* v_key_670_; lean_object* v_val_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_681_; 
v_key_670_ = lean_ctor_get(v_v_661_, 0);
v_val_671_ = lean_ctor_get(v_v_661_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_v_661_);
if (v_isSharedCheck_681_ == 0)
{
v___x_673_ = v_v_661_;
v_isShared_674_ = v_isSharedCheck_681_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_val_671_);
lean_inc(v_key_670_);
lean_dec(v_v_661_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_681_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
uint8_t v___x_675_; 
v___x_675_ = l_Lean_instBEqFVarId_beq(v_x_650_, v_key_670_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; 
lean_del_object(v___x_673_);
v___x_676_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_670_, v_val_671_, v_x_650_, v_x_651_);
v___x_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
v___y_665_ = v___x_677_;
goto v___jp_664_;
}
else
{
lean_object* v___x_679_; 
lean_dec(v_val_671_);
lean_dec(v_key_670_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v_x_651_);
lean_ctor_set(v___x_673_, 0, v_x_650_);
v___x_679_ = v___x_673_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_x_650_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_x_651_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
v___y_665_ = v___x_679_;
goto v___jp_664_;
}
}
}
}
case 1:
{
lean_object* v_node_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_694_; 
v_node_682_ = lean_ctor_get(v_v_661_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v_v_661_);
if (v_isSharedCheck_694_ == 0)
{
v___x_684_ = v_v_661_;
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_node_682_);
lean_dec(v_v_661_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_686_ = ((size_t)5ULL);
v___x_687_ = lean_usize_shift_right(v_x_648_, v___x_686_);
v___x_688_ = ((size_t)1ULL);
v___x_689_ = lean_usize_add(v_x_649_, v___x_688_);
v___x_690_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_682_, v___x_687_, v___x_689_, v_x_650_, v_x_651_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_690_);
v___x_692_ = v___x_684_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v___y_665_ = v___x_692_;
goto v___jp_664_;
}
}
}
default: 
{
lean_object* v___x_695_; 
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_x_650_);
lean_ctor_set(v___x_695_, 1, v_x_651_);
v___y_665_ = v___x_695_;
goto v___jp_664_;
}
}
v___jp_664_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = lean_array_fset(v_xs_x27_663_, v_j_655_, v___y_665_);
lean_dec(v_j_655_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_666_);
v___x_668_ = v___x_659_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
else
{
lean_object* v_ks_698_; lean_object* v_vs_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_719_; 
v_ks_698_ = lean_ctor_get(v_x_647_, 0);
v_vs_699_ = lean_ctor_get(v_x_647_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_x_647_);
if (v_isSharedCheck_719_ == 0)
{
v___x_701_ = v_x_647_;
v_isShared_702_ = v_isSharedCheck_719_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_vs_699_);
lean_inc(v_ks_698_);
lean_dec(v_x_647_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_719_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_ks_698_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_vs_699_);
v___x_704_ = v_reuseFailAlloc_718_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v_newNode_705_; uint8_t v___y_707_; size_t v___x_713_; uint8_t v___x_714_; 
v_newNode_705_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_704_, v_x_650_, v_x_651_);
v___x_713_ = ((size_t)7ULL);
v___x_714_ = lean_usize_dec_le(v___x_713_, v_x_649_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_705_);
v___x_716_ = lean_unsigned_to_nat(4u);
v___x_717_ = lean_nat_dec_lt(v___x_715_, v___x_716_);
lean_dec(v___x_715_);
v___y_707_ = v___x_717_;
goto v___jp_706_;
}
else
{
v___y_707_ = v___x_714_;
goto v___jp_706_;
}
v___jp_706_:
{
if (v___y_707_ == 0)
{
lean_object* v_ks_708_; lean_object* v_vs_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_ks_708_ = lean_ctor_get(v_newNode_705_, 0);
lean_inc_ref(v_ks_708_);
v_vs_709_ = lean_ctor_get(v_newNode_705_, 1);
lean_inc_ref(v_vs_709_);
lean_dec_ref(v_newNode_705_);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_712_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_649_, v_ks_708_, v_vs_709_, v___x_710_, v___x_711_);
lean_dec_ref(v_vs_709_);
lean_dec_ref(v_ks_708_);
return v___x_712_;
}
else
{
return v_newNode_705_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(size_t v_depth_720_, lean_object* v_keys_721_, lean_object* v_vals_722_, lean_object* v_i_723_, lean_object* v_entries_724_){
_start:
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = lean_array_get_size(v_keys_721_);
v___x_726_ = lean_nat_dec_lt(v_i_723_, v___x_725_);
if (v___x_726_ == 0)
{
lean_dec(v_i_723_);
return v_entries_724_;
}
else
{
lean_object* v_k_727_; lean_object* v_v_728_; uint64_t v___x_729_; size_t v_h_730_; size_t v___x_731_; lean_object* v___x_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; size_t v_h_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_k_727_ = lean_array_fget_borrowed(v_keys_721_, v_i_723_);
v_v_728_ = lean_array_fget_borrowed(v_vals_722_, v_i_723_);
v___x_729_ = l_Lean_instHashableFVarId_hash(v_k_727_);
v_h_730_ = lean_uint64_to_usize(v___x_729_);
v___x_731_ = ((size_t)5ULL);
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = ((size_t)1ULL);
v___x_734_ = lean_usize_sub(v_depth_720_, v___x_733_);
v___x_735_ = lean_usize_mul(v___x_731_, v___x_734_);
v_h_736_ = lean_usize_shift_right(v_h_730_, v___x_735_);
v___x_737_ = lean_nat_add(v_i_723_, v___x_732_);
lean_dec(v_i_723_);
lean_inc(v_v_728_);
lean_inc(v_k_727_);
v___x_738_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_entries_724_, v_h_736_, v_depth_720_, v_k_727_, v_v_728_);
v_i_723_ = v___x_737_;
v_entries_724_ = v___x_738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_740_, lean_object* v_keys_741_, lean_object* v_vals_742_, lean_object* v_i_743_, lean_object* v_entries_744_){
_start:
{
size_t v_depth_boxed_745_; lean_object* v_res_746_; 
v_depth_boxed_745_ = lean_unbox_usize(v_depth_740_);
lean_dec(v_depth_740_);
v_res_746_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_boxed_745_, v_keys_741_, v_vals_742_, v_i_743_, v_entries_744_);
lean_dec_ref(v_vals_742_);
lean_dec_ref(v_keys_741_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___boxed(lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
size_t v_x_357__boxed_752_; size_t v_x_358__boxed_753_; lean_object* v_res_754_; 
v_x_357__boxed_752_ = lean_unbox_usize(v_x_748_);
lean_dec(v_x_748_);
v_x_358__boxed_753_ = lean_unbox_usize(v_x_749_);
lean_dec(v_x_749_);
v_res_754_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_747_, v_x_357__boxed_752_, v_x_358__boxed_753_, v_x_750_, v_x_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
uint64_t v___x_758_; size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_758_ = l_Lean_instHashableFVarId_hash(v_x_756_);
v___x_759_ = lean_uint64_to_usize(v___x_758_);
v___x_760_ = ((size_t)1ULL);
v___x_761_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_755_, v___x_759_, v___x_760_, v_x_756_, v_x_757_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object* v_lctx_762_, lean_object* v_fvarId_763_, lean_object* v_userName_764_, lean_object* v_type_765_, uint8_t v_bi_766_, uint8_t v_kind_767_){
_start:
{
lean_object* v_decls_768_; lean_object* v_fvarIdToDecl_769_; lean_object* v_auxDeclToFullName_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_782_; 
v_decls_768_ = lean_ctor_get(v_lctx_762_, 1);
v_fvarIdToDecl_769_ = lean_ctor_get(v_lctx_762_, 0);
v_auxDeclToFullName_770_ = lean_ctor_get(v_lctx_762_, 2);
v_isSharedCheck_782_ = !lean_is_exclusive(v_lctx_762_);
if (v_isSharedCheck_782_ == 0)
{
v___x_772_ = v_lctx_762_;
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_auxDeclToFullName_770_);
lean_inc(v_decls_768_);
lean_inc(v_fvarIdToDecl_769_);
lean_dec(v_lctx_762_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_size_774_; lean_object* v_decl_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v_size_774_ = lean_ctor_get(v_decls_768_, 2);
lean_inc(v_fvarId_763_);
lean_inc(v_size_774_);
v_decl_775_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_775_, 0, v_size_774_);
lean_ctor_set(v_decl_775_, 1, v_fvarId_763_);
lean_ctor_set(v_decl_775_, 2, v_userName_764_);
lean_ctor_set(v_decl_775_, 3, v_type_765_);
lean_ctor_set_uint8(v_decl_775_, sizeof(void*)*4, v_bi_766_);
lean_ctor_set_uint8(v_decl_775_, sizeof(void*)*4 + 1, v_kind_767_);
lean_inc_ref(v_decl_775_);
v___x_776_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_769_, v_fvarId_763_, v_decl_775_);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v_decl_775_);
v___x_778_ = l_Lean_PersistentArray_push___redArg(v_decls_768_, v___x_777_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_778_);
lean_ctor_set(v___x_772_, 0, v___x_776_);
v___x_780_ = v___x_772_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_auxDeclToFullName_770_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLocalDecl___boxed(lean_object* v_lctx_783_, lean_object* v_fvarId_784_, lean_object* v_userName_785_, lean_object* v_type_786_, lean_object* v_bi_787_, lean_object* v_kind_788_){
_start:
{
uint8_t v_bi_boxed_789_; uint8_t v_kind_boxed_790_; lean_object* v_res_791_; 
v_bi_boxed_789_ = lean_unbox(v_bi_787_);
v_kind_boxed_790_ = lean_unbox(v_kind_788_);
v_res_791_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_783_, v_fvarId_784_, v_userName_785_, v_type_786_, v_bi_boxed_789_, v_kind_boxed_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0(lean_object* v_00_u03b2_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_x_793_, v_x_794_, v_x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, size_t v_x_799_, size_t v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_798_, v_x_799_, v_x_800_, v_x_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_804_, lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_){
_start:
{
size_t v_x_561__boxed_810_; size_t v_x_562__boxed_811_; lean_object* v_res_812_; 
v_x_561__boxed_810_ = lean_unbox_usize(v_x_806_);
lean_dec(v_x_806_);
v_x_562__boxed_811_ = lean_unbox_usize(v_x_807_);
lean_dec(v_x_807_);
v_res_812_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0(v_00_u03b2_804_, v_x_805_, v_x_561__boxed_810_, v_x_562__boxed_811_, v_x_808_, v_x_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_813_, lean_object* v_n_814_, lean_object* v_k_815_, lean_object* v_v_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v_n_814_, v_k_815_, v_v_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_818_, size_t v_depth_819_, lean_object* v_keys_820_, lean_object* v_vals_821_, lean_object* v_heq_822_, lean_object* v_i_823_, lean_object* v_entries_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_depth_819_, v_keys_820_, v_vals_821_, v_i_823_, v_entries_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_826_, lean_object* v_depth_827_, lean_object* v_keys_828_, lean_object* v_vals_829_, lean_object* v_heq_830_, lean_object* v_i_831_, lean_object* v_entries_832_){
_start:
{
size_t v_depth_boxed_833_; lean_object* v_res_834_; 
v_depth_boxed_833_ = lean_unbox_usize(v_depth_827_);
lean_dec(v_depth_827_);
v_res_834_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2(v_00_u03b2_826_, v_depth_boxed_833_, v_keys_828_, v_vals_829_, v_heq_830_, v_i_831_, v_entries_832_);
lean_dec_ref(v_vals_829_);
lean_dec_ref(v_keys_828_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_x_836_, v_x_837_, v_x_838_, v_x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_local_decl(lean_object* v_lctx_841_, lean_object* v_fvarId_842_, lean_object* v_userName_843_, lean_object* v_type_844_, uint8_t v_bi_845_){
_start:
{
uint8_t v___x_846_; lean_object* v___x_847_; 
v___x_846_ = 0;
v___x_847_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_841_, v_fvarId_842_, v_userName_843_, v_type_844_, v_bi_845_, v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLocalDeclExported___boxed(lean_object* v_lctx_848_, lean_object* v_fvarId_849_, lean_object* v_userName_850_, lean_object* v_type_851_, lean_object* v_bi_852_){
_start:
{
uint8_t v_bi_boxed_853_; lean_object* v_res_854_; 
v_bi_boxed_853_ = lean_unbox(v_bi_852_);
v_res_854_ = lean_local_ctx_mk_local_decl(v_lctx_848_, v_fvarId_849_, v_userName_850_, v_type_851_, v_bi_boxed_853_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl(lean_object* v_lctx_855_, lean_object* v_fvarId_856_, lean_object* v_userName_857_, lean_object* v_type_858_, lean_object* v_value_859_, uint8_t v_nondep_860_, uint8_t v_kind_861_){
_start:
{
lean_object* v_decls_862_; lean_object* v_fvarIdToDecl_863_; lean_object* v_auxDeclToFullName_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_876_; 
v_decls_862_ = lean_ctor_get(v_lctx_855_, 1);
v_fvarIdToDecl_863_ = lean_ctor_get(v_lctx_855_, 0);
v_auxDeclToFullName_864_ = lean_ctor_get(v_lctx_855_, 2);
v_isSharedCheck_876_ = !lean_is_exclusive(v_lctx_855_);
if (v_isSharedCheck_876_ == 0)
{
v___x_866_ = v_lctx_855_;
v_isShared_867_ = v_isSharedCheck_876_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_auxDeclToFullName_864_);
lean_inc(v_decls_862_);
lean_inc(v_fvarIdToDecl_863_);
lean_dec(v_lctx_855_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_876_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_size_868_; lean_object* v_decl_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
v_size_868_ = lean_ctor_get(v_decls_862_, 2);
lean_inc(v_fvarId_856_);
lean_inc(v_size_868_);
v_decl_869_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_decl_869_, 0, v_size_868_);
lean_ctor_set(v_decl_869_, 1, v_fvarId_856_);
lean_ctor_set(v_decl_869_, 2, v_userName_857_);
lean_ctor_set(v_decl_869_, 3, v_type_858_);
lean_ctor_set(v_decl_869_, 4, v_value_859_);
lean_ctor_set_uint8(v_decl_869_, sizeof(void*)*5, v_nondep_860_);
lean_ctor_set_uint8(v_decl_869_, sizeof(void*)*5 + 1, v_kind_861_);
lean_inc_ref(v_decl_869_);
v___x_870_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_863_, v_fvarId_856_, v_decl_869_);
v___x_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_871_, 0, v_decl_869_);
v___x_872_ = l_Lean_PersistentArray_push___redArg(v_decls_862_, v___x_871_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v___x_872_);
lean_ctor_set(v___x_866_, 0, v___x_870_);
v___x_874_ = v___x_866_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_auxDeclToFullName_864_);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLetDecl___boxed(lean_object* v_lctx_877_, lean_object* v_fvarId_878_, lean_object* v_userName_879_, lean_object* v_type_880_, lean_object* v_value_881_, lean_object* v_nondep_882_, lean_object* v_kind_883_){
_start:
{
uint8_t v_nondep_boxed_884_; uint8_t v_kind_boxed_885_; lean_object* v_res_886_; 
v_nondep_boxed_884_ = lean_unbox(v_nondep_882_);
v_kind_boxed_885_ = lean_unbox(v_kind_883_);
v_res_886_ = l_Lean_LocalContext_mkLetDecl(v_lctx_877_, v_fvarId_878_, v_userName_879_, v_type_880_, v_value_881_, v_nondep_boxed_884_, v_kind_boxed_885_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_mk_let_decl(lean_object* v_lctx_887_, lean_object* v_fvarId_888_, lean_object* v_userName_889_, lean_object* v_type_890_, lean_object* v_value_891_, uint8_t v_nondep_892_){
_start:
{
uint8_t v___x_893_; lean_object* v___x_894_; 
v___x_893_ = 0;
v___x_894_ = l_Lean_LocalContext_mkLetDecl(v_lctx_887_, v_fvarId_888_, v_userName_889_, v_type_890_, v_value_891_, v_nondep_892_, v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_mkLetDeclExported___boxed(lean_object* v_lctx_895_, lean_object* v_fvarId_896_, lean_object* v_userName_897_, lean_object* v_type_898_, lean_object* v_value_899_, lean_object* v_nondep_900_){
_start:
{
uint8_t v_nondep_boxed_901_; lean_object* v_res_902_; 
v_nondep_boxed_901_ = lean_unbox(v_nondep_900_);
v_res_902_ = lean_local_ctx_mk_let_decl(v_lctx_895_, v_fvarId_896_, v_userName_897_, v_type_898_, v_value_899_, v_nondep_boxed_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object* v_lctx_903_, lean_object* v_fvarId_904_, lean_object* v_userName_905_, lean_object* v_type_906_, lean_object* v_fullName_907_){
_start:
{
lean_object* v_decls_908_; lean_object* v_fvarIdToDecl_909_; lean_object* v_auxDeclToFullName_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_925_; 
v_decls_908_ = lean_ctor_get(v_lctx_903_, 1);
v_fvarIdToDecl_909_ = lean_ctor_get(v_lctx_903_, 0);
v_auxDeclToFullName_910_ = lean_ctor_get(v_lctx_903_, 2);
v_isSharedCheck_925_ = !lean_is_exclusive(v_lctx_903_);
if (v_isSharedCheck_925_ == 0)
{
v___x_912_ = v_lctx_903_;
v_isShared_913_ = v_isSharedCheck_925_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_auxDeclToFullName_910_);
lean_inc(v_decls_908_);
lean_inc(v_fvarIdToDecl_909_);
lean_dec(v_lctx_903_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_925_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_size_914_; uint8_t v___x_915_; uint8_t v___x_916_; lean_object* v_decl_917_; lean_object* v_auxDeclToFullName_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v_size_914_ = lean_ctor_get(v_decls_908_, 2);
v___x_915_ = 0;
v___x_916_ = 2;
lean_inc_n(v_fvarId_904_, 2);
lean_inc(v_size_914_);
v_decl_917_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_decl_917_, 0, v_size_914_);
lean_ctor_set(v_decl_917_, 1, v_fvarId_904_);
lean_ctor_set(v_decl_917_, 2, v_userName_905_);
lean_ctor_set(v_decl_917_, 3, v_type_906_);
lean_ctor_set_uint8(v_decl_917_, sizeof(void*)*4, v___x_915_);
lean_ctor_set_uint8(v_decl_917_, sizeof(void*)*4 + 1, v___x_916_);
v_auxDeclToFullName_918_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_904_, v_fullName_907_, v_auxDeclToFullName_910_);
lean_inc_ref(v_decl_917_);
v___x_919_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_909_, v_fvarId_904_, v_decl_917_);
v___x_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_920_, 0, v_decl_917_);
v___x_921_ = l_Lean_PersistentArray_push___redArg(v_decls_908_, v___x_920_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 2, v_auxDeclToFullName_918_);
lean_ctor_set(v___x_912_, 1, v___x_921_);
lean_ctor_set(v___x_912_, 0, v___x_919_);
v___x_923_ = v___x_912_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_auxDeclToFullName_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_addDecl(lean_object* v_lctx_926_, lean_object* v_newDecl_927_){
_start:
{
lean_object* v_decls_928_; lean_object* v_fvarIdToDecl_929_; lean_object* v_auxDeclToFullName_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_945_; 
v_decls_928_ = lean_ctor_get(v_lctx_926_, 1);
v_fvarIdToDecl_929_ = lean_ctor_get(v_lctx_926_, 0);
v_auxDeclToFullName_930_ = lean_ctor_get(v_lctx_926_, 2);
v_isSharedCheck_945_ = !lean_is_exclusive(v_lctx_926_);
if (v_isSharedCheck_945_ == 0)
{
v___x_932_ = v_lctx_926_;
v_isShared_933_ = v_isSharedCheck_945_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_auxDeclToFullName_930_);
lean_inc(v_decls_928_);
lean_inc(v_fvarIdToDecl_929_);
lean_dec(v_lctx_926_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_945_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_size_934_; lean_object* v_newDecl_935_; lean_object* v___y_937_; lean_object* v_fvarId_944_; 
v_size_934_ = lean_ctor_get(v_decls_928_, 2);
lean_inc(v_size_934_);
v_newDecl_935_ = l_Lean_LocalDecl_setIndex(v_newDecl_927_, v_size_934_);
v_fvarId_944_ = lean_ctor_get(v_newDecl_935_, 1);
lean_inc(v_fvarId_944_);
v___y_937_ = v_fvarId_944_;
goto v___jp_936_;
v___jp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
lean_inc_ref(v_newDecl_935_);
v___x_938_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_929_, v___y_937_, v_newDecl_935_);
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v_newDecl_935_);
v___x_940_ = l_Lean_PersistentArray_push___redArg(v_decls_928_, v___x_939_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 1, v___x_940_);
lean_ctor_set(v___x_932_, 0, v___x_938_);
v___x_942_ = v___x_932_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_auxDeclToFullName_930_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_946_, lean_object* v_vals_947_, lean_object* v_i_948_, lean_object* v_k_949_){
_start:
{
lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_950_ = lean_array_get_size(v_keys_946_);
v___x_951_ = lean_nat_dec_lt(v_i_948_, v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
lean_dec(v_i_948_);
v___x_952_ = lean_box(0);
return v___x_952_;
}
else
{
lean_object* v_k_x27_953_; uint8_t v___x_954_; 
v_k_x27_953_ = lean_array_fget_borrowed(v_keys_946_, v_i_948_);
v___x_954_ = l_Lean_instBEqFVarId_beq(v_k_949_, v_k_x27_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_unsigned_to_nat(1u);
v___x_956_ = lean_nat_add(v_i_948_, v___x_955_);
lean_dec(v_i_948_);
v_i_948_ = v___x_956_;
goto _start;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_array_fget_borrowed(v_vals_947_, v_i_948_);
lean_dec(v_i_948_);
lean_inc(v___x_958_);
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_960_, lean_object* v_vals_961_, lean_object* v_i_962_, lean_object* v_k_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_960_, v_vals_961_, v_i_962_, v_k_963_);
lean_dec(v_k_963_);
lean_dec_ref(v_vals_961_);
lean_dec_ref(v_keys_960_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_965_, size_t v_x_966_, lean_object* v_x_967_){
_start:
{
if (lean_obj_tag(v_x_965_) == 0)
{
lean_object* v_es_968_; lean_object* v___x_969_; size_t v___x_970_; size_t v___x_971_; lean_object* v_j_972_; lean_object* v___x_973_; 
v_es_968_ = lean_ctor_get(v_x_965_, 0);
v___x_969_ = lean_box(2);
v___x_970_ = ((size_t)31ULL);
v___x_971_ = lean_usize_land(v_x_966_, v___x_970_);
v_j_972_ = lean_usize_to_nat(v___x_971_);
v___x_973_ = lean_array_get_borrowed(v___x_969_, v_es_968_, v_j_972_);
lean_dec(v_j_972_);
switch(lean_obj_tag(v___x_973_))
{
case 0:
{
lean_object* v_key_974_; lean_object* v_val_975_; uint8_t v___x_976_; 
v_key_974_ = lean_ctor_get(v___x_973_, 0);
v_val_975_ = lean_ctor_get(v___x_973_, 1);
v___x_976_ = l_Lean_instBEqFVarId_beq(v_x_967_, v_key_974_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
v___x_977_ = lean_box(0);
return v___x_977_;
}
else
{
lean_object* v___x_978_; 
lean_inc(v_val_975_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v_val_975_);
return v___x_978_;
}
}
case 1:
{
lean_object* v_node_979_; size_t v___x_980_; size_t v___x_981_; 
v_node_979_ = lean_ctor_get(v___x_973_, 0);
v___x_980_ = ((size_t)5ULL);
v___x_981_ = lean_usize_shift_right(v_x_966_, v___x_980_);
v_x_965_ = v_node_979_;
v_x_966_ = v___x_981_;
goto _start;
}
default: 
{
lean_object* v___x_983_; 
v___x_983_ = lean_box(0);
return v___x_983_;
}
}
}
else
{
lean_object* v_ks_984_; lean_object* v_vs_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_ks_984_ = lean_ctor_get(v_x_965_, 0);
v_vs_985_ = lean_ctor_get(v_x_965_, 1);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_984_, v_vs_985_, v___x_986_, v_x_967_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_988_, lean_object* v_x_989_, lean_object* v_x_990_){
_start:
{
size_t v_x_133__boxed_991_; lean_object* v_res_992_; 
v_x_133__boxed_991_ = lean_unbox_usize(v_x_989_);
lean_dec(v_x_989_);
v_res_992_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_988_, v_x_133__boxed_991_, v_x_990_);
lean_dec(v_x_990_);
lean_dec_ref(v_x_988_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
uint64_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v___x_995_ = l_Lean_instHashableFVarId_hash(v_x_994_);
v___x_996_ = lean_uint64_to_usize(v___x_995_);
v___x_997_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_993_, v___x_996_, v_x_994_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg___boxed(lean_object* v_x_998_, lean_object* v_x_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_998_, v_x_999_);
lean_dec(v_x_999_);
lean_dec_ref(v_x_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_find(lean_object* v_lctx_1001_, lean_object* v_fvarId_1002_){
_start:
{
lean_object* v_fvarIdToDecl_1003_; lean_object* v___x_1004_; 
v_fvarIdToDecl_1003_ = lean_ctor_get(v_lctx_1001_, 0);
lean_inc_ref(v_fvarIdToDecl_1003_);
lean_dec_ref(v_lctx_1001_);
v___x_1004_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_1003_, v_fvarId_1002_);
lean_dec(v_fvarId_1002_);
lean_dec_ref(v_fvarIdToDecl_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(lean_object* v_00_u03b2_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_x_1006_, v_x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0(v_00_u03b2_1009_, v_x_1010_, v_x_1011_);
lean_dec(v_x_1011_);
lean_dec_ref(v_x_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1013_, lean_object* v_x_1014_, size_t v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_1014_, v_x_1015_, v_x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_){
_start:
{
size_t v_x_202__boxed_1022_; lean_object* v_res_1023_; 
v_x_202__boxed_1022_ = lean_unbox_usize(v_x_1020_);
lean_dec(v_x_1020_);
v_res_1023_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1018_, v_x_1019_, v_x_202__boxed_1022_, v_x_1021_);
lean_dec(v_x_1021_);
lean_dec_ref(v_x_1019_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1024_, lean_object* v_keys_1025_, lean_object* v_vals_1026_, lean_object* v_heq_1027_, lean_object* v_i_1028_, lean_object* v_k_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1025_, v_vals_1026_, v_i_1028_, v_k_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1031_, lean_object* v_keys_1032_, lean_object* v_vals_1033_, lean_object* v_heq_1034_, lean_object* v_i_1035_, lean_object* v_k_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1031_, v_keys_1032_, v_vals_1033_, v_heq_1034_, v_i_1035_, v_k_1036_);
lean_dec(v_k_1036_);
lean_dec_ref(v_vals_1033_);
lean_dec_ref(v_keys_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f(lean_object* v_lctx_1038_, lean_object* v_e_1039_){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = l_Lean_Expr_fvarId_x21(v_e_1039_);
v___x_1041_ = lean_local_ctx_find(v_lctx_1038_, v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFVar_x3f___boxed(lean_object* v_lctx_1042_, lean_object* v_e_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_1042_, v_e_1043_);
lean_dec_ref(v_e_1043_);
return v_res_1044_;
}
}
static lean_object* _init_l_Lean_LocalContext_get_x21___closed__2(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1047_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_1048_ = lean_unsigned_to_nat(14u);
v___x_1049_ = lean_unsigned_to_nat(340u);
v___x_1050_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__0));
v___x_1051_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_1052_ = l_mkPanicMessageWithDecl(v___x_1051_, v___x_1050_, v___x_1049_, v___x_1048_, v___x_1047_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_get_x21(lean_object* v_lctx_1053_, lean_object* v_fvarId_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_local_ctx_find(v_lctx_1053_, v_fvarId_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_obj_once(&l_Lean_LocalContext_get_x21___closed__2, &l_Lean_LocalContext_get_x21___closed__2_once, _init_l_Lean_LocalContext_get_x21___closed__2);
v___x_1057_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_1056_);
return v___x_1057_;
}
else
{
lean_object* v_val_1058_; 
v_val_1058_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v___x_1055_, 1);
return v_val_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21(lean_object* v_lctx_1059_, lean_object* v_e_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = l_Lean_Expr_fvarId_x21(v_e_1060_);
v___x_1062_ = l_Lean_LocalContext_get_x21(v_lctx_1059_, v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVar_x21___boxed(lean_object* v_lctx_1063_, lean_object* v_e_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1063_, v_e_1064_);
lean_dec_ref(v_e_1064_);
return v_res_1065_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1066_, lean_object* v_i_1067_, lean_object* v_k_1068_){
_start:
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = lean_array_get_size(v_keys_1066_);
v___x_1070_ = lean_nat_dec_lt(v_i_1067_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec(v_i_1067_);
return v___x_1070_;
}
else
{
lean_object* v_k_x27_1071_; uint8_t v___x_1072_; 
v_k_x27_1071_ = lean_array_fget_borrowed(v_keys_1066_, v_i_1067_);
v___x_1072_ = l_Lean_instBEqFVarId_beq(v_k_1068_, v_k_x27_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_unsigned_to_nat(1u);
v___x_1074_ = lean_nat_add(v_i_1067_, v___x_1073_);
lean_dec(v_i_1067_);
v_i_1067_ = v___x_1074_;
goto _start;
}
else
{
lean_dec(v_i_1067_);
return v___x_1072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1076_, lean_object* v_i_1077_, lean_object* v_k_1078_){
_start:
{
uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1076_, v_i_1077_, v_k_1078_);
lean_dec(v_k_1078_);
lean_dec_ref(v_keys_1076_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(lean_object* v_x_1081_, size_t v_x_1082_, lean_object* v_x_1083_){
_start:
{
if (lean_obj_tag(v_x_1081_) == 0)
{
lean_object* v_es_1084_; lean_object* v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; lean_object* v_j_1088_; lean_object* v___x_1089_; 
v_es_1084_ = lean_ctor_get(v_x_1081_, 0);
v___x_1085_ = lean_box(2);
v___x_1086_ = ((size_t)31ULL);
v___x_1087_ = lean_usize_land(v_x_1082_, v___x_1086_);
v_j_1088_ = lean_usize_to_nat(v___x_1087_);
v___x_1089_ = lean_array_get_borrowed(v___x_1085_, v_es_1084_, v_j_1088_);
lean_dec(v_j_1088_);
switch(lean_obj_tag(v___x_1089_))
{
case 0:
{
lean_object* v_key_1090_; uint8_t v___x_1091_; 
v_key_1090_ = lean_ctor_get(v___x_1089_, 0);
v___x_1091_ = l_Lean_instBEqFVarId_beq(v_x_1083_, v_key_1090_);
return v___x_1091_;
}
case 1:
{
lean_object* v_node_1092_; size_t v___x_1093_; size_t v___x_1094_; 
v_node_1092_ = lean_ctor_get(v___x_1089_, 0);
v___x_1093_ = ((size_t)5ULL);
v___x_1094_ = lean_usize_shift_right(v_x_1082_, v___x_1093_);
v_x_1081_ = v_node_1092_;
v_x_1082_ = v___x_1094_;
goto _start;
}
default: 
{
uint8_t v___x_1096_; 
v___x_1096_ = 0;
return v___x_1096_;
}
}
}
else
{
lean_object* v_ks_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_ks_1097_ = lean_ctor_get(v_x_1081_, 0);
v___x_1098_ = lean_unsigned_to_nat(0u);
v___x_1099_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_ks_1097_, v___x_1098_, v_x_1083_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
size_t v_x_119__boxed_1103_; uint8_t v_res_1104_; lean_object* v_r_1105_; 
v_x_119__boxed_1103_ = lean_unbox_usize(v_x_1101_);
lean_dec(v_x_1101_);
v_res_1104_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1100_, v_x_119__boxed_1103_, v_x_1102_);
lean_dec(v_x_1102_);
lean_dec_ref(v_x_1100_);
v_r_1105_ = lean_box(v_res_1104_);
return v_r_1105_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
uint64_t v___x_1108_; size_t v___x_1109_; uint8_t v___x_1110_; 
v___x_1108_ = l_Lean_instHashableFVarId_hash(v_x_1107_);
v___x_1109_ = lean_uint64_to_usize(v___x_1108_);
v___x_1110_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1106_, v___x_1109_, v_x_1107_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg___boxed(lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
uint8_t v_res_1113_; lean_object* v_r_1114_; 
v_res_1113_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1111_, v_x_1112_);
lean_dec(v_x_1112_);
lean_dec_ref(v_x_1111_);
v_r_1114_ = lean_box(v_res_1113_);
return v_r_1114_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_contains(lean_object* v_lctx_1115_, lean_object* v_fvarId_1116_){
_start:
{
lean_object* v_fvarIdToDecl_1117_; uint8_t v___x_1118_; 
v_fvarIdToDecl_1117_ = lean_ctor_get(v_lctx_1115_, 0);
v___x_1118_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_fvarIdToDecl_1117_, v_fvarId_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_contains___boxed(lean_object* v_lctx_1119_, lean_object* v_fvarId_1120_){
_start:
{
uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_res_1121_ = l_Lean_LocalContext_contains(v_lctx_1119_, v_fvarId_1120_);
lean_dec(v_fvarId_1120_);
lean_dec_ref(v_lctx_1119_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(lean_object* v_00_u03b2_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___redArg(v_x_1124_, v_x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0___boxed(lean_object* v_00_u03b2_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0(v_00_u03b2_1127_, v_x_1128_, v_x_1129_);
lean_dec(v_x_1129_);
lean_dec_ref(v_x_1128_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(lean_object* v_00_u03b2_1132_, lean_object* v_x_1133_, size_t v_x_1134_, lean_object* v_x_1135_){
_start:
{
uint8_t v___x_1136_; 
v___x_1136_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___redArg(v_x_1133_, v_x_1134_, v_x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1137_, lean_object* v_x_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
size_t v_x_182__boxed_1141_; uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_x_182__boxed_1141_ = lean_unbox_usize(v_x_1139_);
lean_dec(v_x_1139_);
v_res_1142_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0(v_00_u03b2_1137_, v_x_1138_, v_x_182__boxed_1141_, v_x_1140_);
lean_dec(v_x_1140_);
lean_dec_ref(v_x_1138_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1144_, lean_object* v_keys_1145_, lean_object* v_vals_1146_, lean_object* v_heq_1147_, lean_object* v_i_1148_, lean_object* v_k_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___redArg(v_keys_1145_, v_i_1148_, v_k_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1151_, lean_object* v_keys_1152_, lean_object* v_vals_1153_, lean_object* v_heq_1154_, lean_object* v_i_1155_, lean_object* v_k_1156_){
_start:
{
uint8_t v_res_1157_; lean_object* v_r_1158_; 
v_res_1157_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_LocalContext_contains_spec__0_spec__0_spec__1(v_00_u03b2_1151_, v_keys_1152_, v_vals_1153_, v_heq_1154_, v_i_1155_, v_k_1156_);
lean_dec(v_k_1156_);
lean_dec_ref(v_vals_1153_);
lean_dec_ref(v_keys_1152_);
v_r_1158_ = lean_box(v_res_1157_);
return v_r_1158_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_containsFVar(lean_object* v_lctx_1159_, lean_object* v_e_1160_){
_start:
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = l_Lean_Expr_fvarId_x21(v_e_1160_);
v___x_1162_ = l_Lean_LocalContext_contains(v_lctx_1159_, v___x_1161_);
lean_dec(v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_containsFVar___boxed(lean_object* v_lctx_1163_, lean_object* v_e_1164_){
_start:
{
uint8_t v_res_1165_; lean_object* v_r_1166_; 
v_res_1165_ = l_Lean_LocalContext_containsFVar(v_lctx_1163_, v_e_1164_);
lean_dec_ref(v_e_1164_);
lean_dec_ref(v_lctx_1163_);
v_r_1166_ = lean_box(v_res_1165_);
return v_r_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(lean_object* v_as_1167_, size_t v_i_1168_, size_t v_stop_1169_, lean_object* v_b_1170_){
_start:
{
lean_object* v___y_1172_; uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_eq(v_i_1168_, v_stop_1169_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_array_uget_borrowed(v_as_1167_, v_i_1168_);
if (lean_obj_tag(v___x_1177_) == 0)
{
v___y_1172_ = v_b_1170_;
goto v___jp_1171_;
}
else
{
lean_object* v_val_1178_; lean_object* v_fvarId_1179_; lean_object* v___x_1180_; 
v_val_1178_ = lean_ctor_get(v___x_1177_, 0);
v_fvarId_1179_ = lean_ctor_get(v_val_1178_, 1);
lean_inc(v_fvarId_1179_);
v___x_1180_ = lean_array_push(v_b_1170_, v_fvarId_1179_);
v___y_1172_ = v___x_1180_;
goto v___jp_1171_;
}
}
else
{
return v_b_1170_;
}
v___jp_1171_:
{
size_t v___x_1173_; size_t v___x_1174_; 
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_add(v_i_1168_, v___x_1173_);
v_i_1168_ = v___x_1174_;
v_b_1170_ = v___y_1172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1___boxed(lean_object* v_as_1181_, lean_object* v_i_1182_, lean_object* v_stop_1183_, lean_object* v_b_1184_){
_start:
{
size_t v_i_boxed_1185_; size_t v_stop_boxed_1186_; lean_object* v_res_1187_; 
v_i_boxed_1185_ = lean_unbox_usize(v_i_1182_);
lean_dec(v_i_1182_);
v_stop_boxed_1186_ = lean_unbox_usize(v_stop_1183_);
lean_dec(v_stop_1183_);
v_res_1187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_as_1181_, v_i_boxed_1185_, v_stop_boxed_1186_, v_b_1184_);
lean_dec_ref(v_as_1181_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(lean_object* v_x_1188_, lean_object* v_x_1189_){
_start:
{
if (lean_obj_tag(v_x_1188_) == 0)
{
lean_object* v_cs_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_cs_1190_ = lean_ctor_get(v_x_1188_, 0);
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_array_get_size(v_cs_1190_);
v___x_1193_ = lean_nat_dec_lt(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
return v_x_1189_;
}
else
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_nat_dec_le(v___x_1192_, v___x_1192_);
if (v___x_1194_ == 0)
{
if (v___x_1193_ == 0)
{
return v_x_1189_;
}
else
{
size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = ((size_t)0ULL);
v___x_1196_ = lean_usize_of_nat(v___x_1192_);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1190_, v___x_1195_, v___x_1196_, v_x_1189_);
return v___x_1197_;
}
}
else
{
size_t v___x_1198_; size_t v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = ((size_t)0ULL);
v___x_1199_ = lean_usize_of_nat(v___x_1192_);
v___x_1200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1190_, v___x_1198_, v___x_1199_, v_x_1189_);
return v___x_1200_;
}
}
}
else
{
lean_object* v_vs_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v_vs_1201_ = lean_ctor_get(v_x_1188_, 0);
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = lean_array_get_size(v_vs_1201_);
v___x_1204_ = lean_nat_dec_lt(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
return v_x_1189_;
}
else
{
uint8_t v___x_1205_; 
v___x_1205_ = lean_nat_dec_le(v___x_1203_, v___x_1203_);
if (v___x_1205_ == 0)
{
if (v___x_1204_ == 0)
{
return v_x_1189_;
}
else
{
size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = lean_usize_of_nat(v___x_1203_);
v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1201_, v___x_1206_, v___x_1207_, v_x_1189_);
return v___x_1208_;
}
}
else
{
size_t v___x_1209_; size_t v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = ((size_t)0ULL);
v___x_1210_ = lean_usize_of_nat(v___x_1203_);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1201_, v___x_1209_, v___x_1210_, v_x_1189_);
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1212_, size_t v_i_1213_, size_t v_stop_1214_, lean_object* v_b_1215_){
_start:
{
uint8_t v___x_1216_; 
v___x_1216_ = lean_usize_dec_eq(v_i_1213_, v_stop_1214_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; 
v___x_1217_ = lean_array_uget_borrowed(v_as_1212_, v_i_1213_);
v___x_1218_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1217_, v_b_1215_);
v___x_1219_ = ((size_t)1ULL);
v___x_1220_ = lean_usize_add(v_i_1213_, v___x_1219_);
v_i_1213_ = v___x_1220_;
v_b_1215_ = v___x_1218_;
goto _start;
}
else
{
return v_b_1215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1222_, lean_object* v_i_1223_, lean_object* v_stop_1224_, lean_object* v_b_1225_){
_start:
{
size_t v_i_boxed_1226_; size_t v_stop_boxed_1227_; lean_object* v_res_1228_; 
v_i_boxed_1226_ = lean_unbox_usize(v_i_1223_);
lean_dec(v_i_1223_);
v_stop_boxed_1227_ = lean_unbox_usize(v_stop_1224_);
lean_dec(v_stop_1224_);
v_res_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1222_, v_i_boxed_1226_, v_stop_boxed_1227_, v_b_1225_);
lean_dec_ref(v_as_1222_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1229_, lean_object* v_x_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1229_, v_x_1230_);
lean_dec_ref(v_x_1229_);
return v_res_1231_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1233_, size_t v_x_1234_, size_t v_x_1235_, lean_object* v_x_1236_){
_start:
{
if (lean_obj_tag(v_x_1233_) == 0)
{
lean_object* v_cs_1237_; lean_object* v___x_1238_; size_t v___x_1239_; lean_object* v_j_1240_; lean_object* v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_cs_1237_ = lean_ctor_get(v_x_1233_, 0);
v___x_1238_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1239_ = lean_usize_shift_right(v_x_1234_, v_x_1235_);
v_j_1240_ = lean_usize_to_nat(v___x_1239_);
v___x_1241_ = lean_array_get_borrowed(v___x_1238_, v_cs_1237_, v_j_1240_);
v___x_1242_ = ((size_t)1ULL);
v___x_1243_ = lean_usize_shift_left(v___x_1242_, v_x_1235_);
v___x_1244_ = lean_usize_sub(v___x_1243_, v___x_1242_);
v___x_1245_ = lean_usize_land(v_x_1234_, v___x_1244_);
v___x_1246_ = ((size_t)5ULL);
v___x_1247_ = lean_usize_sub(v_x_1235_, v___x_1246_);
v___x_1248_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1241_, v___x_1245_, v___x_1247_, v_x_1236_);
v___x_1249_ = lean_unsigned_to_nat(1u);
v___x_1250_ = lean_nat_add(v_j_1240_, v___x_1249_);
lean_dec(v_j_1240_);
v___x_1251_ = lean_array_get_size(v_cs_1237_);
v___x_1252_ = lean_nat_dec_lt(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_dec(v___x_1250_);
return v___x_1248_;
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = lean_nat_dec_le(v___x_1251_, v___x_1251_);
if (v___x_1253_ == 0)
{
if (v___x_1252_ == 0)
{
lean_dec(v___x_1250_);
return v___x_1248_;
}
else
{
size_t v___x_1254_; size_t v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_usize_of_nat(v___x_1250_);
lean_dec(v___x_1250_);
v___x_1255_ = lean_usize_of_nat(v___x_1251_);
v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1237_, v___x_1254_, v___x_1255_, v___x_1248_);
return v___x_1256_;
}
}
else
{
size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_usize_of_nat(v___x_1250_);
lean_dec(v___x_1250_);
v___x_1258_ = lean_usize_of_nat(v___x_1251_);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1237_, v___x_1257_, v___x_1258_, v___x_1248_);
return v___x_1259_;
}
}
}
else
{
lean_object* v_vs_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_vs_1260_ = lean_ctor_get(v_x_1233_, 0);
v___x_1261_ = lean_usize_to_nat(v_x_1234_);
v___x_1262_ = lean_array_get_size(v_vs_1260_);
v___x_1263_ = lean_nat_dec_lt(v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_dec(v___x_1261_);
return v_x_1236_;
}
else
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_nat_dec_le(v___x_1262_, v___x_1262_);
if (v___x_1264_ == 0)
{
if (v___x_1263_ == 0)
{
lean_dec(v___x_1261_);
return v_x_1236_;
}
else
{
size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_usize_of_nat(v___x_1261_);
lean_dec(v___x_1261_);
v___x_1266_ = lean_usize_of_nat(v___x_1262_);
v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1260_, v___x_1265_, v___x_1266_, v_x_1236_);
return v___x_1267_;
}
}
else
{
size_t v___x_1268_; size_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = lean_usize_of_nat(v___x_1261_);
lean_dec(v___x_1261_);
v___x_1269_ = lean_usize_of_nat(v___x_1262_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1260_, v___x_1268_, v___x_1269_, v_x_1236_);
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
size_t v_x_1632__boxed_1275_; size_t v_x_1633__boxed_1276_; lean_object* v_res_1277_; 
v_x_1632__boxed_1275_ = lean_unbox_usize(v_x_1272_);
lean_dec(v_x_1272_);
v_x_1633__boxed_1276_ = lean_unbox_usize(v_x_1273_);
lean_dec(v_x_1273_);
v_res_1277_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1271_, v_x_1632__boxed_1275_, v_x_1633__boxed_1276_, v_x_1274_);
lean_dec_ref(v_x_1271_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1278_, lean_object* v_init_1279_, lean_object* v_start_1280_){
_start:
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_nat_dec_eq(v_start_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v_root_1283_; lean_object* v_tail_1284_; size_t v_shift_1285_; lean_object* v_tailOff_1286_; uint8_t v___x_1287_; 
v_root_1283_ = lean_ctor_get(v_t_1278_, 0);
v_tail_1284_ = lean_ctor_get(v_t_1278_, 1);
v_shift_1285_ = lean_ctor_get_usize(v_t_1278_, 4);
v_tailOff_1286_ = lean_ctor_get(v_t_1278_, 3);
v___x_1287_ = lean_nat_dec_le(v_tailOff_1286_, v_start_1280_);
if (v___x_1287_ == 0)
{
size_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1288_ = lean_usize_of_nat(v_start_1280_);
v___x_1289_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1283_, v___x_1288_, v_shift_1285_, v_init_1279_);
v___x_1290_ = lean_array_get_size(v_tail_1284_);
v___x_1291_ = lean_nat_dec_lt(v___x_1281_, v___x_1290_);
if (v___x_1291_ == 0)
{
return v___x_1289_;
}
else
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_nat_dec_le(v___x_1290_, v___x_1290_);
if (v___x_1292_ == 0)
{
if (v___x_1291_ == 0)
{
return v___x_1289_;
}
else
{
size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = ((size_t)0ULL);
v___x_1294_ = lean_usize_of_nat(v___x_1290_);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1284_, v___x_1293_, v___x_1294_, v___x_1289_);
return v___x_1295_;
}
}
else
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = lean_usize_of_nat(v___x_1290_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1284_, v___x_1296_, v___x_1297_, v___x_1289_);
return v___x_1298_;
}
}
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1299_ = lean_nat_sub(v_start_1280_, v_tailOff_1286_);
v___x_1300_ = lean_array_get_size(v_tail_1284_);
v___x_1301_ = lean_nat_dec_lt(v___x_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_dec(v___x_1299_);
return v_init_1279_;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_nat_dec_le(v___x_1300_, v___x_1300_);
if (v___x_1302_ == 0)
{
if (v___x_1301_ == 0)
{
lean_dec(v___x_1299_);
return v_init_1279_;
}
else
{
size_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_usize_of_nat(v___x_1299_);
lean_dec(v___x_1299_);
v___x_1304_ = lean_usize_of_nat(v___x_1300_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1284_, v___x_1303_, v___x_1304_, v_init_1279_);
return v___x_1305_;
}
}
else
{
size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_usize_of_nat(v___x_1299_);
lean_dec(v___x_1299_);
v___x_1307_ = lean_usize_of_nat(v___x_1300_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1284_, v___x_1306_, v___x_1307_, v_init_1279_);
return v___x_1308_;
}
}
}
}
else
{
lean_object* v_root_1309_; lean_object* v_tail_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_root_1309_ = lean_ctor_get(v_t_1278_, 0);
v_tail_1310_ = lean_ctor_get(v_t_1278_, 1);
v___x_1311_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1309_, v_init_1279_);
v___x_1312_ = lean_array_get_size(v_tail_1310_);
v___x_1313_ = lean_nat_dec_lt(v___x_1281_, v___x_1312_);
if (v___x_1313_ == 0)
{
return v___x_1311_;
}
else
{
uint8_t v___x_1314_; 
v___x_1314_ = lean_nat_dec_le(v___x_1312_, v___x_1312_);
if (v___x_1314_ == 0)
{
if (v___x_1313_ == 0)
{
return v___x_1311_;
}
else
{
size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = lean_usize_of_nat(v___x_1312_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1310_, v___x_1315_, v___x_1316_, v___x_1311_);
return v___x_1317_;
}
}
else
{
size_t v___x_1318_; size_t v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = ((size_t)0ULL);
v___x_1319_ = lean_usize_of_nat(v___x_1312_);
v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1310_, v___x_1318_, v___x_1319_, v___x_1311_);
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1321_, lean_object* v_init_1322_, lean_object* v_start_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1321_, v_init_1322_, v_start_1323_);
lean_dec(v_start_1323_);
lean_dec_ref(v_t_1321_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1327_){
_start:
{
lean_object* v_decls_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_decls_1328_ = lean_ctor_get(v_lctx_1327_, 1);
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1331_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1328_, v___x_1330_, v___x_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_LocalContext_getFVarIds(v_lctx_1332_);
lean_dec_ref(v_lctx_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1334_, size_t v_i_1335_, lean_object* v_bs_1336_){
_start:
{
uint8_t v___x_1337_; 
v___x_1337_ = lean_usize_dec_lt(v_i_1335_, v_sz_1334_);
if (v___x_1337_ == 0)
{
return v_bs_1336_;
}
else
{
lean_object* v_v_1338_; lean_object* v___x_1339_; lean_object* v_bs_x27_1340_; lean_object* v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v_v_1338_ = lean_array_uget(v_bs_1336_, v_i_1335_);
v___x_1339_ = lean_unsigned_to_nat(0u);
v_bs_x27_1340_ = lean_array_uset(v_bs_1336_, v_i_1335_, v___x_1339_);
v___x_1341_ = l_Lean_mkFVar(v_v_1338_);
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = lean_usize_add(v_i_1335_, v___x_1342_);
v___x_1344_ = lean_array_uset(v_bs_x27_1340_, v_i_1335_, v___x_1341_);
v_i_1335_ = v___x_1343_;
v_bs_1336_ = v___x_1344_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1346_, lean_object* v_i_1347_, lean_object* v_bs_1348_){
_start:
{
size_t v_sz_boxed_1349_; size_t v_i_boxed_1350_; lean_object* v_res_1351_; 
v_sz_boxed_1349_ = lean_unbox_usize(v_sz_1346_);
lean_dec(v_sz_1346_);
v_i_boxed_1350_ = lean_unbox_usize(v_i_1347_);
lean_dec(v_i_1347_);
v_res_1351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1349_, v_i_boxed_1350_, v_bs_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1352_){
_start:
{
lean_object* v___x_1353_; size_t v_sz_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1353_ = l_Lean_LocalContext_getFVarIds(v_lctx_1352_);
v_sz_1354_ = lean_array_size(v___x_1353_);
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1354_, v___x_1355_, v___x_1353_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_LocalContext_getFVars(v_lctx_1357_);
lean_dec_ref(v_lctx_1357_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1359_){
_start:
{
lean_object* v_size_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_size_1360_ = lean_ctor_get(v_a_1359_, 2);
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = lean_nat_dec_eq(v_size_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_unsigned_to_nat(1u);
v___x_1365_ = lean_nat_sub(v_size_1360_, v___x_1364_);
v___x_1366_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1363_, v_a_1359_, v___x_1365_);
lean_dec(v___x_1365_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_PersistentArray_pop___redArg(v_a_1359_);
v_a_1359_ = v___x_1367_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1366_, 1);
return v_a_1359_;
}
}
else
{
return v_a_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1369_, lean_object* v_t_1370_){
_start:
{
if (lean_obj_tag(v_t_1370_) == 0)
{
lean_object* v_k_1371_; lean_object* v_v_1372_; lean_object* v_l_1373_; lean_object* v_r_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_2028_; 
v_k_1371_ = lean_ctor_get(v_t_1370_, 1);
v_v_1372_ = lean_ctor_get(v_t_1370_, 2);
v_l_1373_ = lean_ctor_get(v_t_1370_, 3);
v_r_1374_ = lean_ctor_get(v_t_1370_, 4);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_t_1370_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v_t_1370_, 0);
lean_dec(v_unused_2029_);
v___x_1376_ = v_t_1370_;
v_isShared_1377_ = v_isSharedCheck_2028_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_r_1374_);
lean_inc(v_l_1373_);
lean_inc(v_v_1372_);
lean_inc(v_k_1371_);
lean_dec(v_t_1370_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_2028_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
uint8_t v___x_1378_; 
v___x_1378_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1369_, v_k_1371_);
switch(v___x_1378_)
{
case 0:
{
lean_object* v_impl_1379_; lean_object* v___x_1380_; 
v_impl_1379_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1369_, v_l_1373_);
v___x_1380_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1379_) == 0)
{
if (lean_obj_tag(v_r_1374_) == 0)
{
lean_object* v_size_1381_; lean_object* v_size_1382_; lean_object* v_k_1383_; lean_object* v_v_1384_; lean_object* v_l_1385_; lean_object* v_r_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v_size_1381_ = lean_ctor_get(v_impl_1379_, 0);
lean_inc(v_size_1381_);
v_size_1382_ = lean_ctor_get(v_r_1374_, 0);
v_k_1383_ = lean_ctor_get(v_r_1374_, 1);
v_v_1384_ = lean_ctor_get(v_r_1374_, 2);
v_l_1385_ = lean_ctor_get(v_r_1374_, 3);
lean_inc(v_l_1385_);
v_r_1386_ = lean_ctor_get(v_r_1374_, 4);
v___x_1387_ = lean_unsigned_to_nat(3u);
v___x_1388_ = lean_nat_mul(v___x_1387_, v_size_1381_);
v___x_1389_ = lean_nat_dec_lt(v___x_1388_, v_size_1382_);
lean_dec(v___x_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
lean_dec(v_l_1385_);
v___x_1390_ = lean_nat_add(v___x_1380_, v_size_1381_);
lean_dec(v_size_1381_);
v___x_1391_ = lean_nat_add(v___x_1390_, v_size_1382_);
lean_dec(v___x_1390_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 3, v_impl_1379_);
lean_ctor_set(v___x_1376_, 0, v___x_1391_);
v___x_1393_ = v___x_1376_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_impl_1379_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_r_1374_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
else
{
lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1458_; 
lean_inc(v_r_1386_);
lean_inc(v_v_1384_);
lean_inc(v_k_1383_);
lean_inc(v_size_1382_);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_r_1374_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; lean_object* v_unused_1462_; lean_object* v_unused_1463_; 
v_unused_1459_ = lean_ctor_get(v_r_1374_, 4);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_r_1374_, 3);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_r_1374_, 2);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_r_1374_, 1);
lean_dec(v_unused_1462_);
v_unused_1463_ = lean_ctor_get(v_r_1374_, 0);
lean_dec(v_unused_1463_);
v___x_1396_ = v_r_1374_;
v_isShared_1397_ = v_isSharedCheck_1458_;
goto v_resetjp_1395_;
}
else
{
lean_dec(v_r_1374_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1458_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_size_1398_; lean_object* v_k_1399_; lean_object* v_v_1400_; lean_object* v_l_1401_; lean_object* v_r_1402_; lean_object* v_size_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_size_1398_ = lean_ctor_get(v_l_1385_, 0);
v_k_1399_ = lean_ctor_get(v_l_1385_, 1);
v_v_1400_ = lean_ctor_get(v_l_1385_, 2);
v_l_1401_ = lean_ctor_get(v_l_1385_, 3);
v_r_1402_ = lean_ctor_get(v_l_1385_, 4);
v_size_1403_ = lean_ctor_get(v_r_1386_, 0);
v___x_1404_ = lean_unsigned_to_nat(2u);
v___x_1405_ = lean_nat_mul(v___x_1404_, v_size_1403_);
v___x_1406_ = lean_nat_dec_lt(v_size_1398_, v___x_1405_);
lean_dec(v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1434_; 
lean_inc(v_r_1402_);
lean_inc(v_l_1401_);
lean_inc(v_v_1400_);
lean_inc(v_k_1399_);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_l_1385_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; lean_object* v_unused_1439_; 
v_unused_1435_ = lean_ctor_get(v_l_1385_, 4);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_l_1385_, 3);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_l_1385_, 2);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_l_1385_, 1);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_l_1385_, 0);
lean_dec(v_unused_1439_);
v___x_1408_ = v_l_1385_;
v_isShared_1409_ = v_isSharedCheck_1434_;
goto v_resetjp_1407_;
}
else
{
lean_dec(v_l_1385_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1434_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1424_; 
v___x_1410_ = lean_nat_add(v___x_1380_, v_size_1381_);
lean_dec(v_size_1381_);
v___x_1411_ = lean_nat_add(v___x_1410_, v_size_1382_);
lean_dec(v_size_1382_);
if (lean_obj_tag(v_l_1401_) == 0)
{
lean_object* v_size_1432_; 
v_size_1432_ = lean_ctor_get(v_l_1401_, 0);
lean_inc(v_size_1432_);
v___y_1424_ = v_size_1432_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___y_1424_ = v___x_1433_;
goto v___jp_1423_;
}
v___jp_1412_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_nat_add(v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec(v___y_1414_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 4, v_r_1386_);
lean_ctor_set(v___x_1408_, 3, v_r_1402_);
lean_ctor_set(v___x_1408_, 2, v_v_1384_);
lean_ctor_set(v___x_1408_, 1, v_k_1383_);
lean_ctor_set(v___x_1408_, 0, v___x_1416_);
v___x_1418_ = v___x_1408_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_k_1383_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_v_1384_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_r_1402_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_r_1386_);
v___x_1418_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v___x_1418_);
lean_ctor_set(v___x_1396_, 3, v___y_1413_);
lean_ctor_set(v___x_1396_, 2, v_v_1400_);
lean_ctor_set(v___x_1396_, 1, v_k_1399_);
lean_ctor_set(v___x_1396_, 0, v___x_1411_);
v___x_1420_ = v___x_1396_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v___y_1413_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
v___jp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_nat_add(v___x_1410_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec(v___x_1410_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_l_1401_);
lean_ctor_set(v___x_1376_, 3, v_impl_1379_);
lean_ctor_set(v___x_1376_, 0, v___x_1425_);
v___x_1427_ = v___x_1376_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_impl_1379_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v_l_1401_);
v___x_1427_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_nat_add(v___x_1380_, v_size_1403_);
if (lean_obj_tag(v_r_1402_) == 0)
{
lean_object* v_size_1429_; 
v_size_1429_ = lean_ctor_get(v_r_1402_, 0);
lean_inc(v_size_1429_);
v___y_1413_ = v___x_1427_;
v___y_1414_ = v___x_1428_;
v___y_1415_ = v_size_1429_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_unsigned_to_nat(0u);
v___y_1413_ = v___x_1427_;
v___y_1414_ = v___x_1428_;
v___y_1415_ = v___x_1430_;
goto v___jp_1412_;
}
}
}
}
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
lean_del_object(v___x_1376_);
v___x_1440_ = lean_nat_add(v___x_1380_, v_size_1381_);
lean_dec(v_size_1381_);
v___x_1441_ = lean_nat_add(v___x_1440_, v_size_1382_);
lean_dec(v_size_1382_);
v___x_1442_ = lean_nat_add(v___x_1440_, v_size_1398_);
lean_dec(v___x_1440_);
lean_inc_ref(v_impl_1379_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v_l_1385_);
lean_ctor_set(v___x_1396_, 3, v_impl_1379_);
lean_ctor_set(v___x_1396_, 2, v_v_1372_);
lean_ctor_set(v___x_1396_, 1, v_k_1371_);
lean_ctor_set(v___x_1396_, 0, v___x_1442_);
v___x_1444_ = v___x_1396_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_impl_1379_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_l_1385_);
v___x_1444_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
v_isSharedCheck_1451_ = !lean_is_exclusive(v_impl_1379_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; lean_object* v_unused_1455_; lean_object* v_unused_1456_; 
v_unused_1452_ = lean_ctor_get(v_impl_1379_, 4);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_impl_1379_, 3);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_impl_1379_, 2);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_impl_1379_, 1);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_impl_1379_, 0);
lean_dec(v_unused_1456_);
v___x_1446_ = v_impl_1379_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v_impl_1379_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 4, v_r_1386_);
lean_ctor_set(v___x_1446_, 3, v___x_1444_);
lean_ctor_set(v___x_1446_, 2, v_v_1384_);
lean_ctor_set(v___x_1446_, 1, v_k_1383_);
lean_ctor_set(v___x_1446_, 0, v___x_1441_);
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_k_1383_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_v_1384_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_r_1386_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
v_size_1464_ = lean_ctor_get(v_impl_1379_, 0);
lean_inc(v_size_1464_);
v___x_1465_ = lean_nat_add(v___x_1380_, v_size_1464_);
lean_dec(v_size_1464_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 3, v_impl_1379_);
lean_ctor_set(v___x_1376_, 0, v___x_1465_);
v___x_1467_ = v___x_1376_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_impl_1379_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v_r_1374_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
if (lean_obj_tag(v_r_1374_) == 0)
{
lean_object* v_l_1469_; 
v_l_1469_ = lean_ctor_get(v_r_1374_, 3);
lean_inc(v_l_1469_);
if (lean_obj_tag(v_l_1469_) == 0)
{
lean_object* v_r_1470_; 
v_r_1470_ = lean_ctor_get(v_r_1374_, 4);
lean_inc(v_r_1470_);
if (lean_obj_tag(v_r_1470_) == 0)
{
lean_object* v_size_1471_; lean_object* v_k_1472_; lean_object* v_v_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1486_; 
v_size_1471_ = lean_ctor_get(v_r_1374_, 0);
v_k_1472_ = lean_ctor_get(v_r_1374_, 1);
v_v_1473_ = lean_ctor_get(v_r_1374_, 2);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_r_1374_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; lean_object* v_unused_1488_; 
v_unused_1487_ = lean_ctor_get(v_r_1374_, 4);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_r_1374_, 3);
lean_dec(v_unused_1488_);
v___x_1475_ = v_r_1374_;
v_isShared_1476_ = v_isSharedCheck_1486_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_v_1473_);
lean_inc(v_k_1472_);
lean_inc(v_size_1471_);
lean_dec(v_r_1374_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1486_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_size_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v_size_1477_ = lean_ctor_get(v_l_1469_, 0);
v___x_1478_ = lean_nat_add(v___x_1380_, v_size_1471_);
lean_dec(v_size_1471_);
v___x_1479_ = lean_nat_add(v___x_1380_, v_size_1477_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v_l_1469_);
lean_ctor_set(v___x_1475_, 3, v_impl_1379_);
lean_ctor_set(v___x_1475_, 2, v_v_1372_);
lean_ctor_set(v___x_1475_, 1, v_k_1371_);
lean_ctor_set(v___x_1475_, 0, v___x_1479_);
v___x_1481_ = v___x_1475_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_impl_1379_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_l_1469_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_r_1470_);
lean_ctor_set(v___x_1376_, 3, v___x_1481_);
lean_ctor_set(v___x_1376_, 2, v_v_1473_);
lean_ctor_set(v___x_1376_, 1, v_k_1472_);
lean_ctor_set(v___x_1376_, 0, v___x_1478_);
v___x_1483_ = v___x_1376_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1472_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1473_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_r_1470_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1513_; 
v_k_1489_ = lean_ctor_get(v_r_1374_, 1);
v_v_1490_ = lean_ctor_get(v_r_1374_, 2);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_r_1374_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; lean_object* v_unused_1515_; lean_object* v_unused_1516_; 
v_unused_1514_ = lean_ctor_get(v_r_1374_, 4);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v_r_1374_, 3);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_r_1374_, 0);
lean_dec(v_unused_1516_);
v___x_1492_ = v_r_1374_;
v_isShared_1493_ = v_isSharedCheck_1513_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_v_1490_);
lean_inc(v_k_1489_);
lean_dec(v_r_1374_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1513_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_k_1494_; lean_object* v_v_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1509_; 
v_k_1494_ = lean_ctor_get(v_l_1469_, 1);
v_v_1495_ = lean_ctor_get(v_l_1469_, 2);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_l_1469_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; lean_object* v_unused_1511_; lean_object* v_unused_1512_; 
v_unused_1510_ = lean_ctor_get(v_l_1469_, 4);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_l_1469_, 3);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v_l_1469_, 0);
lean_dec(v_unused_1512_);
v___x_1497_ = v_l_1469_;
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_v_1495_);
lean_inc(v_k_1494_);
lean_dec(v_l_1469_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1509_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = lean_unsigned_to_nat(3u);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 4, v_r_1470_);
lean_ctor_set(v___x_1497_, 3, v_r_1470_);
lean_ctor_set(v___x_1497_, 2, v_v_1372_);
lean_ctor_set(v___x_1497_, 1, v_k_1371_);
lean_ctor_set(v___x_1497_, 0, v___x_1380_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_r_1470_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_r_1470_);
v___x_1501_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 3, v_r_1470_);
lean_ctor_set(v___x_1492_, 0, v___x_1380_);
v___x_1503_ = v___x_1492_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_r_1470_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v_r_1470_);
v___x_1503_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v___x_1503_);
lean_ctor_set(v___x_1376_, 3, v___x_1501_);
lean_ctor_set(v___x_1376_, 2, v_v_1495_);
lean_ctor_set(v___x_1376_, 1, v_k_1494_);
lean_ctor_set(v___x_1376_, 0, v___x_1499_);
v___x_1505_ = v___x_1376_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_k_1494_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_v_1495_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1517_; 
v_r_1517_ = lean_ctor_get(v_r_1374_, 4);
lean_inc(v_r_1517_);
if (lean_obj_tag(v_r_1517_) == 0)
{
lean_object* v_k_1518_; lean_object* v_v_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1530_; 
v_k_1518_ = lean_ctor_get(v_r_1374_, 1);
v_v_1519_ = lean_ctor_get(v_r_1374_, 2);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_r_1374_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; lean_object* v_unused_1532_; lean_object* v_unused_1533_; 
v_unused_1531_ = lean_ctor_get(v_r_1374_, 4);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v_r_1374_, 3);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_r_1374_, 0);
lean_dec(v_unused_1533_);
v___x_1521_ = v_r_1374_;
v_isShared_1522_ = v_isSharedCheck_1530_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_v_1519_);
lean_inc(v_k_1518_);
lean_dec(v_r_1374_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1530_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = lean_unsigned_to_nat(3u);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 4, v_l_1469_);
lean_ctor_set(v___x_1521_, 2, v_v_1372_);
lean_ctor_set(v___x_1521_, 1, v_k_1371_);
lean_ctor_set(v___x_1521_, 0, v___x_1380_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_l_1469_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_l_1469_);
v___x_1525_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_r_1517_);
lean_ctor_set(v___x_1376_, 3, v___x_1525_);
lean_ctor_set(v___x_1376_, 2, v_v_1519_);
lean_ctor_set(v___x_1376_, 1, v_k_1518_);
lean_ctor_set(v___x_1376_, 0, v___x_1523_);
v___x_1527_ = v___x_1376_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_k_1518_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_v_1519_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_r_1517_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_size_1534_; lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1547_; 
v_size_1534_ = lean_ctor_get(v_r_1374_, 0);
v_k_1535_ = lean_ctor_get(v_r_1374_, 1);
v_v_1536_ = lean_ctor_get(v_r_1374_, 2);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_r_1374_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; lean_object* v_unused_1549_; 
v_unused_1548_ = lean_ctor_get(v_r_1374_, 4);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_r_1374_, 3);
lean_dec(v_unused_1549_);
v___x_1538_ = v_r_1374_;
v_isShared_1539_ = v_isSharedCheck_1547_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_v_1536_);
lean_inc(v_k_1535_);
lean_inc(v_size_1534_);
lean_dec(v_r_1374_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1547_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 3, v_r_1517_);
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_size_1534_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_k_1535_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_v_1536_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_r_1517_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_r_1517_);
v___x_1541_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_unsigned_to_nat(2u);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v___x_1541_);
lean_ctor_set(v___x_1376_, 3, v_r_1517_);
lean_ctor_set(v___x_1376_, 0, v___x_1542_);
v___x_1544_ = v___x_1376_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_r_1517_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v___x_1541_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
}
else
{
lean_object* v___x_1551_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 3, v_r_1374_);
lean_ctor_set(v___x_1376_, 0, v___x_1380_);
v___x_1551_ = v___x_1376_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_r_1374_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v_r_1374_);
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
case 1:
{
lean_del_object(v___x_1376_);
lean_dec(v_v_1372_);
lean_dec(v_k_1371_);
if (lean_obj_tag(v_l_1373_) == 0)
{
if (lean_obj_tag(v_r_1374_) == 0)
{
lean_object* v_size_1553_; lean_object* v_k_1554_; lean_object* v_v_1555_; lean_object* v_l_1556_; lean_object* v_r_1557_; lean_object* v_size_1558_; lean_object* v_k_1559_; lean_object* v_v_1560_; lean_object* v_l_1561_; lean_object* v_r_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_size_1553_ = lean_ctor_get(v_l_1373_, 0);
v_k_1554_ = lean_ctor_get(v_l_1373_, 1);
v_v_1555_ = lean_ctor_get(v_l_1373_, 2);
v_l_1556_ = lean_ctor_get(v_l_1373_, 3);
v_r_1557_ = lean_ctor_get(v_l_1373_, 4);
lean_inc(v_r_1557_);
v_size_1558_ = lean_ctor_get(v_r_1374_, 0);
v_k_1559_ = lean_ctor_get(v_r_1374_, 1);
v_v_1560_ = lean_ctor_get(v_r_1374_, 2);
v_l_1561_ = lean_ctor_get(v_r_1374_, 3);
lean_inc(v_l_1561_);
v_r_1562_ = lean_ctor_get(v_r_1374_, 4);
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = lean_nat_dec_lt(v_size_1553_, v_size_1558_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1700_; 
lean_inc(v_l_1556_);
lean_inc(v_v_1555_);
lean_inc(v_k_1554_);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_l_1373_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; lean_object* v_unused_1702_; lean_object* v_unused_1703_; lean_object* v_unused_1704_; lean_object* v_unused_1705_; 
v_unused_1701_ = lean_ctor_get(v_l_1373_, 4);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_l_1373_, 3);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_l_1373_, 2);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v_l_1373_, 1);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_l_1373_, 0);
lean_dec(v_unused_1705_);
v___x_1566_ = v_l_1373_;
v_isShared_1567_ = v_isSharedCheck_1700_;
goto v_resetjp_1565_;
}
else
{
lean_dec(v_l_1373_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1700_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v_tree_1569_; 
v___x_1568_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1554_, v_v_1555_, v_l_1556_, v_r_1557_);
v_tree_1569_ = lean_ctor_get(v___x_1568_, 2);
lean_inc(v_tree_1569_);
if (lean_obj_tag(v_tree_1569_) == 0)
{
lean_object* v_k_1570_; lean_object* v_v_1571_; lean_object* v_size_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_k_1570_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_k_1570_);
v_v_1571_ = lean_ctor_get(v___x_1568_, 1);
lean_inc(v_v_1571_);
lean_dec_ref(v___x_1568_);
v_size_1572_ = lean_ctor_get(v_tree_1569_, 0);
v___x_1573_ = lean_unsigned_to_nat(3u);
v___x_1574_ = lean_nat_mul(v___x_1573_, v_size_1572_);
v___x_1575_ = lean_nat_dec_lt(v___x_1574_, v_size_1558_);
lean_dec(v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
lean_dec(v_l_1561_);
v___x_1576_ = lean_nat_add(v___x_1563_, v_size_1572_);
v___x_1577_ = lean_nat_add(v___x_1576_, v_size_1558_);
lean_dec(v___x_1576_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 4, v_r_1374_);
lean_ctor_set(v___x_1566_, 3, v_tree_1569_);
lean_ctor_set(v___x_1566_, 2, v_v_1571_);
lean_ctor_set(v___x_1566_, 1, v_k_1570_);
lean_ctor_set(v___x_1566_, 0, v___x_1577_);
v___x_1579_ = v___x_1566_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_k_1570_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_v_1571_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_tree_1569_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_r_1374_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
else
{
lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1635_; 
lean_inc(v_r_1562_);
lean_inc(v_v_1560_);
lean_inc(v_k_1559_);
lean_inc(v_size_1558_);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_r_1374_);
if (v_isSharedCheck_1635_ == 0)
{
lean_object* v_unused_1636_; lean_object* v_unused_1637_; lean_object* v_unused_1638_; lean_object* v_unused_1639_; lean_object* v_unused_1640_; 
v_unused_1636_ = lean_ctor_get(v_r_1374_, 4);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_r_1374_, 3);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_r_1374_, 2);
lean_dec(v_unused_1638_);
v_unused_1639_ = lean_ctor_get(v_r_1374_, 1);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_r_1374_, 0);
lean_dec(v_unused_1640_);
v___x_1582_ = v_r_1374_;
v_isShared_1583_ = v_isSharedCheck_1635_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v_r_1374_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1635_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v_size_1584_; lean_object* v_k_1585_; lean_object* v_v_1586_; lean_object* v_l_1587_; lean_object* v_r_1588_; lean_object* v_size_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v_size_1584_ = lean_ctor_get(v_l_1561_, 0);
v_k_1585_ = lean_ctor_get(v_l_1561_, 1);
v_v_1586_ = lean_ctor_get(v_l_1561_, 2);
v_l_1587_ = lean_ctor_get(v_l_1561_, 3);
v_r_1588_ = lean_ctor_get(v_l_1561_, 4);
v_size_1589_ = lean_ctor_get(v_r_1562_, 0);
v___x_1590_ = lean_unsigned_to_nat(2u);
v___x_1591_ = lean_nat_mul(v___x_1590_, v_size_1589_);
v___x_1592_ = lean_nat_dec_lt(v_size_1584_, v___x_1591_);
lean_dec(v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1620_; 
lean_inc(v_r_1588_);
lean_inc(v_l_1587_);
lean_inc(v_v_1586_);
lean_inc(v_k_1585_);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_l_1561_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; lean_object* v_unused_1622_; lean_object* v_unused_1623_; lean_object* v_unused_1624_; lean_object* v_unused_1625_; 
v_unused_1621_ = lean_ctor_get(v_l_1561_, 4);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_l_1561_, 3);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_l_1561_, 2);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_l_1561_, 1);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_l_1561_, 0);
lean_dec(v_unused_1625_);
v___x_1594_ = v_l_1561_;
v_isShared_1595_ = v_isSharedCheck_1620_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v_l_1561_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1620_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1610_; 
v___x_1596_ = lean_nat_add(v___x_1563_, v_size_1572_);
v___x_1597_ = lean_nat_add(v___x_1596_, v_size_1558_);
lean_dec(v_size_1558_);
if (lean_obj_tag(v_l_1587_) == 0)
{
lean_object* v_size_1618_; 
v_size_1618_ = lean_ctor_get(v_l_1587_, 0);
lean_inc(v_size_1618_);
v___y_1610_ = v_size_1618_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_unsigned_to_nat(0u);
v___y_1610_ = v___x_1619_;
goto v___jp_1609_;
}
v___jp_1598_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = lean_nat_add(v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec(v___y_1600_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 4, v_r_1562_);
lean_ctor_set(v___x_1594_, 3, v_r_1588_);
lean_ctor_set(v___x_1594_, 2, v_v_1560_);
lean_ctor_set(v___x_1594_, 1, v_k_1559_);
lean_ctor_set(v___x_1594_, 0, v___x_1602_);
v___x_1604_ = v___x_1594_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1559_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1560_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v_r_1588_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v_r_1562_);
v___x_1604_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1606_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 4, v___x_1604_);
lean_ctor_set(v___x_1582_, 3, v___y_1599_);
lean_ctor_set(v___x_1582_, 2, v_v_1586_);
lean_ctor_set(v___x_1582_, 1, v_k_1585_);
lean_ctor_set(v___x_1582_, 0, v___x_1597_);
v___x_1606_ = v___x_1582_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_k_1585_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_v_1586_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v___y_1599_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
v___jp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = lean_nat_add(v___x_1596_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec(v___x_1596_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 4, v_l_1587_);
lean_ctor_set(v___x_1566_, 3, v_tree_1569_);
lean_ctor_set(v___x_1566_, 2, v_v_1571_);
lean_ctor_set(v___x_1566_, 1, v_k_1570_);
lean_ctor_set(v___x_1566_, 0, v___x_1611_);
v___x_1613_ = v___x_1566_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_k_1570_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_v_1571_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v_tree_1569_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v_l_1587_);
v___x_1613_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_nat_add(v___x_1563_, v_size_1589_);
if (lean_obj_tag(v_r_1588_) == 0)
{
lean_object* v_size_1615_; 
v_size_1615_ = lean_ctor_get(v_r_1588_, 0);
lean_inc(v_size_1615_);
v___y_1599_ = v___x_1613_;
v___y_1600_ = v___x_1614_;
v___y_1601_ = v_size_1615_;
goto v___jp_1598_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_unsigned_to_nat(0u);
v___y_1599_ = v___x_1613_;
v___y_1600_ = v___x_1614_;
v___y_1601_ = v___x_1616_;
goto v___jp_1598_;
}
}
}
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1626_ = lean_nat_add(v___x_1563_, v_size_1572_);
v___x_1627_ = lean_nat_add(v___x_1626_, v_size_1558_);
lean_dec(v_size_1558_);
v___x_1628_ = lean_nat_add(v___x_1626_, v_size_1584_);
lean_dec(v___x_1626_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 4, v_l_1561_);
lean_ctor_set(v___x_1582_, 3, v_tree_1569_);
lean_ctor_set(v___x_1582_, 2, v_v_1571_);
lean_ctor_set(v___x_1582_, 1, v_k_1570_);
lean_ctor_set(v___x_1582_, 0, v___x_1628_);
v___x_1630_ = v___x_1582_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_k_1570_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_v_1571_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v_tree_1569_);
lean_ctor_set(v_reuseFailAlloc_1634_, 4, v_l_1561_);
v___x_1630_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1632_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 4, v_r_1562_);
lean_ctor_set(v___x_1566_, 3, v___x_1630_);
lean_ctor_set(v___x_1566_, 2, v_v_1560_);
lean_ctor_set(v___x_1566_, 1, v_k_1559_);
lean_ctor_set(v___x_1566_, 0, v___x_1627_);
v___x_1632_ = v___x_1566_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_k_1559_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_v_1560_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1633_, 4, v_r_1562_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
}
else
{
lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1694_; 
lean_inc(v_r_1562_);
lean_inc(v_v_1560_);
lean_inc(v_k_1559_);
lean_inc(v_size_1558_);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_r_1374_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; lean_object* v_unused_1696_; lean_object* v_unused_1697_; lean_object* v_unused_1698_; lean_object* v_unused_1699_; 
v_unused_1695_ = lean_ctor_get(v_r_1374_, 4);
lean_dec(v_unused_1695_);
v_unused_1696_ = lean_ctor_get(v_r_1374_, 3);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_r_1374_, 2);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_r_1374_, 1);
lean_dec(v_unused_1698_);
v_unused_1699_ = lean_ctor_get(v_r_1374_, 0);
lean_dec(v_unused_1699_);
v___x_1642_ = v_r_1374_;
v_isShared_1643_ = v_isSharedCheck_1694_;
goto v_resetjp_1641_;
}
else
{
lean_dec(v_r_1374_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1694_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
if (lean_obj_tag(v_l_1561_) == 0)
{
if (lean_obj_tag(v_r_1562_) == 0)
{
lean_object* v_k_1644_; lean_object* v_v_1645_; lean_object* v_size_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
v_k_1644_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_k_1644_);
v_v_1645_ = lean_ctor_get(v___x_1568_, 1);
lean_inc(v_v_1645_);
lean_dec_ref(v___x_1568_);
v_size_1646_ = lean_ctor_get(v_l_1561_, 0);
v___x_1647_ = lean_nat_add(v___x_1563_, v_size_1558_);
lean_dec(v_size_1558_);
v___x_1648_ = lean_nat_add(v___x_1563_, v_size_1646_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 4, v_l_1561_);
lean_ctor_set(v___x_1642_, 3, v_tree_1569_);
lean_ctor_set(v___x_1642_, 2, v_v_1645_);
lean_ctor_set(v___x_1642_, 1, v_k_1644_);
lean_ctor_set(v___x_1642_, 0, v___x_1648_);
v___x_1650_ = v___x_1642_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1648_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_k_1644_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_v_1645_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v_tree_1569_);
lean_ctor_set(v_reuseFailAlloc_1654_, 4, v_l_1561_);
v___x_1650_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1652_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 4, v_r_1562_);
lean_ctor_set(v___x_1566_, 3, v___x_1650_);
lean_ctor_set(v___x_1566_, 2, v_v_1560_);
lean_ctor_set(v___x_1566_, 1, v_k_1559_);
lean_ctor_set(v___x_1566_, 0, v___x_1647_);
v___x_1652_ = v___x_1566_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_k_1559_);
lean_ctor_set(v_reuseFailAlloc_1653_, 2, v_v_1560_);
lean_ctor_set(v_reuseFailAlloc_1653_, 3, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1653_, 4, v_r_1562_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
else
{
lean_object* v_k_1655_; lean_object* v_v_1656_; lean_object* v_k_1657_; lean_object* v_v_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_size_1558_);
v_k_1655_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_k_1655_);
v_v_1656_ = lean_ctor_get(v___x_1568_, 1);
lean_inc(v_v_1656_);
lean_dec_ref(v___x_1568_);
v_k_1657_ = lean_ctor_get(v_l_1561_, 1);
v_v_1658_ = lean_ctor_get(v_l_1561_, 2);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_l_1561_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; lean_object* v_unused_1674_; lean_object* v_unused_1675_; 
v_unused_1673_ = lean_ctor_get(v_l_1561_, 4);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_l_1561_, 3);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_l_1561_, 0);
lean_dec(v_unused_1675_);
v___x_1660_ = v_l_1561_;
v_isShared_1661_ = v_isSharedCheck_1672_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_v_1658_);
lean_inc(v_k_1657_);
lean_dec(v_l_1561_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1672_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = lean_unsigned_to_nat(3u);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 4, v_r_1562_);
lean_ctor_set(v___x_1660_, 3, v_r_1562_);
lean_ctor_set(v___x_1660_, 2, v_v_1656_);
lean_ctor_set(v___x_1660_, 1, v_k_1655_);
lean_ctor_set(v___x_1660_, 0, v___x_1563_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_k_1655_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_v_1656_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_r_1562_);
lean_ctor_set(v_reuseFailAlloc_1671_, 4, v_r_1562_);
v___x_1664_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 3, v_r_1562_);
lean_ctor_set(v___x_1642_, 0, v___x_1563_);
v___x_1666_ = v___x_1642_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_k_1559_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_v_1560_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v_r_1562_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v_r_1562_);
v___x_1666_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1668_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 4, v___x_1666_);
lean_ctor_set(v___x_1566_, 3, v___x_1664_);
lean_ctor_set(v___x_1566_, 2, v_v_1658_);
lean_ctor_set(v___x_1566_, 1, v_k_1657_);
lean_ctor_set(v___x_1566_, 0, v___x_1662_);
v___x_1668_ = v___x_1566_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1657_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1658_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1562_) == 0)
{
lean_object* v_k_1676_; lean_object* v_v_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
lean_dec(v_size_1558_);
v_k_1676_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_k_1676_);
v_v_1677_ = lean_ctor_get(v___x_1568_, 1);
lean_inc(v_v_1677_);
lean_dec_ref(v___x_1568_);
v___x_1678_ = lean_unsigned_to_nat(3u);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 4, v_l_1561_);
lean_ctor_set(v___x_1642_, 2, v_v_1677_);
lean_ctor_set(v___x_1642_, 1, v_k_1676_);
lean_ctor_set(v___x_1642_, 0, v___x_1563_);
v___x_1680_ = v___x_1642_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_k_1676_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_v_1677_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_l_1561_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_l_1561_);
v___x_1680_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1682_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 4, v_r_1562_);
lean_ctor_set(v___x_1566_, 3, v___x_1680_);
lean_ctor_set(v___x_1566_, 2, v_v_1560_);
lean_ctor_set(v___x_1566_, 1, v_k_1559_);
lean_ctor_set(v___x_1566_, 0, v___x_1678_);
v___x_1682_ = v___x_1566_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_k_1559_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_v_1560_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v_r_1562_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
else
{
lean_object* v_k_1685_; lean_object* v_v_1686_; lean_object* v___x_1688_; 
v_k_1685_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_k_1685_);
v_v_1686_ = lean_ctor_get(v___x_1568_, 1);
lean_inc(v_v_1686_);
lean_dec_ref(v___x_1568_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 3, v_r_1562_);
v___x_1688_ = v___x_1642_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_size_1558_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_k_1559_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_v_1560_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_r_1562_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_r_1562_);
v___x_1688_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = lean_unsigned_to_nat(2u);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 4, v___x_1688_);
lean_ctor_set(v___x_1566_, 3, v_r_1562_);
lean_ctor_set(v___x_1566_, 2, v_v_1686_);
lean_ctor_set(v___x_1566_, 1, v_k_1685_);
lean_ctor_set(v___x_1566_, 0, v___x_1689_);
v___x_1691_ = v___x_1566_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_k_1685_);
lean_ctor_set(v_reuseFailAlloc_1692_, 2, v_v_1686_);
lean_ctor_set(v_reuseFailAlloc_1692_, 3, v_r_1562_);
lean_ctor_set(v_reuseFailAlloc_1692_, 4, v___x_1688_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
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
lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1858_; 
lean_inc(v_r_1562_);
lean_inc(v_v_1560_);
lean_inc(v_k_1559_);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_r_1374_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; lean_object* v_unused_1860_; lean_object* v_unused_1861_; lean_object* v_unused_1862_; lean_object* v_unused_1863_; 
v_unused_1859_ = lean_ctor_get(v_r_1374_, 4);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_r_1374_, 3);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v_r_1374_, 2);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v_r_1374_, 1);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v_r_1374_, 0);
lean_dec(v_unused_1863_);
v___x_1707_ = v_r_1374_;
v_isShared_1708_ = v_isSharedCheck_1858_;
goto v_resetjp_1706_;
}
else
{
lean_dec(v_r_1374_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1858_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v_tree_1710_; 
v___x_1709_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1559_, v_v_1560_, v_l_1561_, v_r_1562_);
v_tree_1710_ = lean_ctor_get(v___x_1709_, 2);
lean_inc(v_tree_1710_);
if (lean_obj_tag(v_tree_1710_) == 0)
{
lean_object* v_k_1711_; lean_object* v_v_1712_; lean_object* v_size_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_k_1711_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_k_1711_);
v_v_1712_ = lean_ctor_get(v___x_1709_, 1);
lean_inc(v_v_1712_);
lean_dec_ref(v___x_1709_);
v_size_1713_ = lean_ctor_get(v_tree_1710_, 0);
v___x_1714_ = lean_unsigned_to_nat(3u);
v___x_1715_ = lean_nat_mul(v___x_1714_, v_size_1713_);
v___x_1716_ = lean_nat_dec_lt(v___x_1715_, v_size_1553_);
lean_dec(v___x_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
lean_dec(v_r_1557_);
v___x_1717_ = lean_nat_add(v___x_1563_, v_size_1553_);
v___x_1718_ = lean_nat_add(v___x_1717_, v_size_1713_);
lean_dec(v___x_1717_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 4, v_tree_1710_);
lean_ctor_set(v___x_1707_, 3, v_l_1373_);
lean_ctor_set(v___x_1707_, 2, v_v_1712_);
lean_ctor_set(v___x_1707_, 1, v_k_1711_);
lean_ctor_set(v___x_1707_, 0, v___x_1718_);
v___x_1720_ = v___x_1707_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_k_1711_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_v_1712_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v_l_1373_);
lean_ctor_set(v_reuseFailAlloc_1721_, 4, v_tree_1710_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
else
{
lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1787_; 
lean_inc(v_l_1556_);
lean_inc(v_v_1555_);
lean_inc(v_k_1554_);
lean_inc(v_size_1553_);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_l_1373_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; lean_object* v_unused_1789_; lean_object* v_unused_1790_; lean_object* v_unused_1791_; lean_object* v_unused_1792_; 
v_unused_1788_ = lean_ctor_get(v_l_1373_, 4);
lean_dec(v_unused_1788_);
v_unused_1789_ = lean_ctor_get(v_l_1373_, 3);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v_l_1373_, 2);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v_l_1373_, 1);
lean_dec(v_unused_1791_);
v_unused_1792_ = lean_ctor_get(v_l_1373_, 0);
lean_dec(v_unused_1792_);
v___x_1723_ = v_l_1373_;
v_isShared_1724_ = v_isSharedCheck_1787_;
goto v_resetjp_1722_;
}
else
{
lean_dec(v_l_1373_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1787_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_size_1725_; lean_object* v_size_1726_; lean_object* v_k_1727_; lean_object* v_v_1728_; lean_object* v_l_1729_; lean_object* v_r_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_size_1725_ = lean_ctor_get(v_l_1556_, 0);
v_size_1726_ = lean_ctor_get(v_r_1557_, 0);
v_k_1727_ = lean_ctor_get(v_r_1557_, 1);
v_v_1728_ = lean_ctor_get(v_r_1557_, 2);
v_l_1729_ = lean_ctor_get(v_r_1557_, 3);
v_r_1730_ = lean_ctor_get(v_r_1557_, 4);
v___x_1731_ = lean_unsigned_to_nat(2u);
v___x_1732_ = lean_nat_mul(v___x_1731_, v_size_1725_);
v___x_1733_ = lean_nat_dec_lt(v_size_1726_, v___x_1732_);
lean_dec(v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1771_; 
lean_inc(v_r_1730_);
lean_inc(v_l_1729_);
lean_inc(v_v_1728_);
lean_inc(v_k_1727_);
lean_del_object(v___x_1723_);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_r_1557_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; lean_object* v_unused_1773_; lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; 
v_unused_1772_ = lean_ctor_get(v_r_1557_, 4);
lean_dec(v_unused_1772_);
v_unused_1773_ = lean_ctor_get(v_r_1557_, 3);
lean_dec(v_unused_1773_);
v_unused_1774_ = lean_ctor_get(v_r_1557_, 2);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_r_1557_, 1);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_r_1557_, 0);
lean_dec(v_unused_1776_);
v___x_1735_ = v_r_1557_;
v_isShared_1736_ = v_isSharedCheck_1771_;
goto v_resetjp_1734_;
}
else
{
lean_dec(v_r_1557_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1771_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___x_1759_; lean_object* v___y_1761_; 
v___x_1737_ = lean_nat_add(v___x_1563_, v_size_1553_);
lean_dec(v_size_1553_);
v___x_1738_ = lean_nat_add(v___x_1737_, v_size_1713_);
lean_dec(v___x_1737_);
v___x_1759_ = lean_nat_add(v___x_1563_, v_size_1725_);
if (lean_obj_tag(v_l_1729_) == 0)
{
lean_object* v_size_1769_; 
v_size_1769_ = lean_ctor_get(v_l_1729_, 0);
lean_inc(v_size_1769_);
v___y_1761_ = v_size_1769_;
goto v___jp_1760_;
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_unsigned_to_nat(0u);
v___y_1761_ = v___x_1770_;
goto v___jp_1760_;
}
v___jp_1739_:
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1743_ = lean_nat_add(v___y_1740_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec(v___y_1740_);
lean_inc_ref(v_tree_1710_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 4, v_tree_1710_);
lean_ctor_set(v___x_1735_, 3, v_r_1730_);
lean_ctor_set(v___x_1735_, 2, v_v_1712_);
lean_ctor_set(v___x_1735_, 1, v_k_1711_);
lean_ctor_set(v___x_1735_, 0, v___x_1743_);
v___x_1745_ = v___x_1735_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_k_1711_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_v_1712_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_r_1730_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_tree_1710_);
v___x_1745_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
v_isSharedCheck_1752_ = !lean_is_exclusive(v_tree_1710_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; lean_object* v_unused_1754_; lean_object* v_unused_1755_; lean_object* v_unused_1756_; lean_object* v_unused_1757_; 
v_unused_1753_ = lean_ctor_get(v_tree_1710_, 4);
lean_dec(v_unused_1753_);
v_unused_1754_ = lean_ctor_get(v_tree_1710_, 3);
lean_dec(v_unused_1754_);
v_unused_1755_ = lean_ctor_get(v_tree_1710_, 2);
lean_dec(v_unused_1755_);
v_unused_1756_ = lean_ctor_get(v_tree_1710_, 1);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v_tree_1710_, 0);
lean_dec(v_unused_1757_);
v___x_1747_ = v_tree_1710_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_dec(v_tree_1710_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 4, v___x_1745_);
lean_ctor_set(v___x_1747_, 3, v___y_1741_);
lean_ctor_set(v___x_1747_, 2, v_v_1728_);
lean_ctor_set(v___x_1747_, 1, v_k_1727_);
lean_ctor_set(v___x_1747_, 0, v___x_1738_);
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_k_1727_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_v_1728_);
lean_ctor_set(v_reuseFailAlloc_1751_, 3, v___y_1741_);
lean_ctor_set(v_reuseFailAlloc_1751_, 4, v___x_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
v___jp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = lean_nat_add(v___x_1759_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec(v___x_1759_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 4, v_l_1729_);
lean_ctor_set(v___x_1707_, 3, v_l_1556_);
lean_ctor_set(v___x_1707_, 2, v_v_1555_);
lean_ctor_set(v___x_1707_, 1, v_k_1554_);
lean_ctor_set(v___x_1707_, 0, v___x_1762_);
v___x_1764_ = v___x_1707_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_l_1556_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v_l_1729_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_nat_add(v___x_1563_, v_size_1713_);
if (lean_obj_tag(v_r_1730_) == 0)
{
lean_object* v_size_1766_; 
v_size_1766_ = lean_ctor_get(v_r_1730_, 0);
lean_inc(v_size_1766_);
v___y_1740_ = v___x_1765_;
v___y_1741_ = v___x_1764_;
v___y_1742_ = v_size_1766_;
goto v___jp_1739_;
}
else
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_unsigned_to_nat(0u);
v___y_1740_ = v___x_1765_;
v___y_1741_ = v___x_1764_;
v___y_1742_ = v___x_1767_;
goto v___jp_1739_;
}
}
}
}
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1777_ = lean_nat_add(v___x_1563_, v_size_1553_);
lean_dec(v_size_1553_);
v___x_1778_ = lean_nat_add(v___x_1777_, v_size_1713_);
lean_dec(v___x_1777_);
v___x_1779_ = lean_nat_add(v___x_1563_, v_size_1713_);
v___x_1780_ = lean_nat_add(v___x_1779_, v_size_1726_);
lean_dec(v___x_1779_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 4, v_tree_1710_);
lean_ctor_set(v___x_1707_, 3, v_r_1557_);
lean_ctor_set(v___x_1707_, 2, v_v_1712_);
lean_ctor_set(v___x_1707_, 1, v_k_1711_);
lean_ctor_set(v___x_1707_, 0, v___x_1780_);
v___x_1782_ = v___x_1707_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_k_1711_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_v_1712_);
lean_ctor_set(v_reuseFailAlloc_1786_, 3, v_r_1557_);
lean_ctor_set(v_reuseFailAlloc_1786_, 4, v_tree_1710_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 4, v___x_1782_);
lean_ctor_set(v___x_1723_, 0, v___x_1778_);
v___x_1784_ = v___x_1723_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_l_1556_);
lean_ctor_set(v_reuseFailAlloc_1785_, 4, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1556_) == 0)
{
lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1816_; 
lean_inc_ref(v_l_1556_);
lean_inc(v_v_1555_);
lean_inc(v_k_1554_);
lean_inc(v_size_1553_);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_l_1373_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; lean_object* v_unused_1818_; lean_object* v_unused_1819_; lean_object* v_unused_1820_; lean_object* v_unused_1821_; 
v_unused_1817_ = lean_ctor_get(v_l_1373_, 4);
lean_dec(v_unused_1817_);
v_unused_1818_ = lean_ctor_get(v_l_1373_, 3);
lean_dec(v_unused_1818_);
v_unused_1819_ = lean_ctor_get(v_l_1373_, 2);
lean_dec(v_unused_1819_);
v_unused_1820_ = lean_ctor_get(v_l_1373_, 1);
lean_dec(v_unused_1820_);
v_unused_1821_ = lean_ctor_get(v_l_1373_, 0);
lean_dec(v_unused_1821_);
v___x_1794_ = v_l_1373_;
v_isShared_1795_ = v_isSharedCheck_1816_;
goto v_resetjp_1793_;
}
else
{
lean_dec(v_l_1373_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1816_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
if (lean_obj_tag(v_r_1557_) == 0)
{
lean_object* v_k_1796_; lean_object* v_v_1797_; lean_object* v_size_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v_k_1796_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_k_1796_);
v_v_1797_ = lean_ctor_get(v___x_1709_, 1);
lean_inc(v_v_1797_);
lean_dec_ref(v___x_1709_);
v_size_1798_ = lean_ctor_get(v_r_1557_, 0);
v___x_1799_ = lean_nat_add(v___x_1563_, v_size_1553_);
lean_dec(v_size_1553_);
v___x_1800_ = lean_nat_add(v___x_1563_, v_size_1798_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 4, v_tree_1710_);
lean_ctor_set(v___x_1707_, 3, v_r_1557_);
lean_ctor_set(v___x_1707_, 2, v_v_1797_);
lean_ctor_set(v___x_1707_, 1, v_k_1796_);
lean_ctor_set(v___x_1707_, 0, v___x_1800_);
v___x_1802_ = v___x_1707_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_k_1796_);
lean_ctor_set(v_reuseFailAlloc_1806_, 2, v_v_1797_);
lean_ctor_set(v_reuseFailAlloc_1806_, 3, v_r_1557_);
lean_ctor_set(v_reuseFailAlloc_1806_, 4, v_tree_1710_);
v___x_1802_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1804_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 4, v___x_1802_);
lean_ctor_set(v___x_1794_, 0, v___x_1799_);
v___x_1804_ = v___x_1794_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1799_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1805_, 3, v_l_1556_);
lean_ctor_set(v_reuseFailAlloc_1805_, 4, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
else
{
lean_object* v_k_1807_; lean_object* v_v_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
lean_dec(v_size_1553_);
v_k_1807_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_k_1807_);
v_v_1808_ = lean_ctor_get(v___x_1709_, 1);
lean_inc(v_v_1808_);
lean_dec_ref(v___x_1709_);
v___x_1809_ = lean_unsigned_to_nat(3u);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 4, v_r_1557_);
lean_ctor_set(v___x_1707_, 3, v_r_1557_);
lean_ctor_set(v___x_1707_, 2, v_v_1808_);
lean_ctor_set(v___x_1707_, 1, v_k_1807_);
lean_ctor_set(v___x_1707_, 0, v___x_1563_);
v___x_1811_ = v___x_1707_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_1815_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_1815_, 3, v_r_1557_);
lean_ctor_set(v_reuseFailAlloc_1815_, 4, v_r_1557_);
v___x_1811_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 4, v___x_1811_);
lean_ctor_set(v___x_1794_, 0, v___x_1809_);
v___x_1813_ = v___x_1794_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1814_, 3, v_l_1556_);
lean_ctor_set(v_reuseFailAlloc_1814_, 4, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1557_) == 0)
{
lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1846_; 
lean_inc(v_l_1556_);
lean_inc(v_v_1555_);
lean_inc(v_k_1554_);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_l_1373_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; lean_object* v_unused_1848_; lean_object* v_unused_1849_; lean_object* v_unused_1850_; lean_object* v_unused_1851_; 
v_unused_1847_ = lean_ctor_get(v_l_1373_, 4);
lean_dec(v_unused_1847_);
v_unused_1848_ = lean_ctor_get(v_l_1373_, 3);
lean_dec(v_unused_1848_);
v_unused_1849_ = lean_ctor_get(v_l_1373_, 2);
lean_dec(v_unused_1849_);
v_unused_1850_ = lean_ctor_get(v_l_1373_, 1);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_l_1373_, 0);
lean_dec(v_unused_1851_);
v___x_1823_ = v_l_1373_;
v_isShared_1824_ = v_isSharedCheck_1846_;
goto v_resetjp_1822_;
}
else
{
lean_dec(v_l_1373_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1846_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_k_1825_; lean_object* v_v_1826_; lean_object* v_k_1827_; lean_object* v_v_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1842_; 
v_k_1825_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_k_1825_);
v_v_1826_ = lean_ctor_get(v___x_1709_, 1);
lean_inc(v_v_1826_);
lean_dec_ref(v___x_1709_);
v_k_1827_ = lean_ctor_get(v_r_1557_, 1);
v_v_1828_ = lean_ctor_get(v_r_1557_, 2);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_r_1557_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; lean_object* v_unused_1844_; lean_object* v_unused_1845_; 
v_unused_1843_ = lean_ctor_get(v_r_1557_, 4);
lean_dec(v_unused_1843_);
v_unused_1844_ = lean_ctor_get(v_r_1557_, 3);
lean_dec(v_unused_1844_);
v_unused_1845_ = lean_ctor_get(v_r_1557_, 0);
lean_dec(v_unused_1845_);
v___x_1830_ = v_r_1557_;
v_isShared_1831_ = v_isSharedCheck_1842_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_v_1828_);
lean_inc(v_k_1827_);
lean_dec(v_r_1557_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1842_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1832_ = lean_unsigned_to_nat(3u);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 4, v_l_1556_);
lean_ctor_set(v___x_1830_, 3, v_l_1556_);
lean_ctor_set(v___x_1830_, 2, v_v_1555_);
lean_ctor_set(v___x_1830_, 1, v_k_1554_);
lean_ctor_set(v___x_1830_, 0, v___x_1563_);
v___x_1834_ = v___x_1830_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_l_1556_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_l_1556_);
v___x_1834_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1836_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 4, v_l_1556_);
lean_ctor_set(v___x_1707_, 3, v_l_1556_);
lean_ctor_set(v___x_1707_, 2, v_v_1826_);
lean_ctor_set(v___x_1707_, 1, v_k_1825_);
lean_ctor_set(v___x_1707_, 0, v___x_1563_);
v___x_1836_ = v___x_1707_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_k_1825_);
lean_ctor_set(v_reuseFailAlloc_1840_, 2, v_v_1826_);
lean_ctor_set(v_reuseFailAlloc_1840_, 3, v_l_1556_);
lean_ctor_set(v_reuseFailAlloc_1840_, 4, v_l_1556_);
v___x_1836_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1838_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 4, v___x_1836_);
lean_ctor_set(v___x_1823_, 3, v___x_1834_);
lean_ctor_set(v___x_1823_, 2, v_v_1828_);
lean_ctor_set(v___x_1823_, 1, v_k_1827_);
lean_ctor_set(v___x_1823_, 0, v___x_1832_);
v___x_1838_ = v___x_1823_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_k_1827_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_v_1828_);
lean_ctor_set(v_reuseFailAlloc_1839_, 3, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1839_, 4, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
}
else
{
lean_object* v_k_1852_; lean_object* v_v_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v_k_1852_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_k_1852_);
v_v_1853_ = lean_ctor_get(v___x_1709_, 1);
lean_inc(v_v_1853_);
lean_dec_ref(v___x_1709_);
v___x_1854_ = lean_unsigned_to_nat(2u);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 4, v_r_1557_);
lean_ctor_set(v___x_1707_, 3, v_l_1373_);
lean_ctor_set(v___x_1707_, 2, v_v_1853_);
lean_ctor_set(v___x_1707_, 1, v_k_1852_);
lean_ctor_set(v___x_1707_, 0, v___x_1854_);
v___x_1856_ = v___x_1707_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_k_1852_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_v_1853_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_l_1373_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_r_1557_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
}
else
{
return v_l_1373_;
}
}
else
{
return v_r_1374_;
}
}
default: 
{
lean_object* v_impl_1864_; lean_object* v___x_1865_; 
v_impl_1864_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1369_, v_r_1374_);
v___x_1865_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1864_) == 0)
{
if (lean_obj_tag(v_l_1373_) == 0)
{
lean_object* v_size_1866_; lean_object* v_size_1867_; lean_object* v_k_1868_; lean_object* v_v_1869_; lean_object* v_l_1870_; lean_object* v_r_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v_size_1866_ = lean_ctor_get(v_impl_1864_, 0);
lean_inc(v_size_1866_);
v_size_1867_ = lean_ctor_get(v_l_1373_, 0);
v_k_1868_ = lean_ctor_get(v_l_1373_, 1);
v_v_1869_ = lean_ctor_get(v_l_1373_, 2);
v_l_1870_ = lean_ctor_get(v_l_1373_, 3);
v_r_1871_ = lean_ctor_get(v_l_1373_, 4);
lean_inc(v_r_1871_);
v___x_1872_ = lean_unsigned_to_nat(3u);
v___x_1873_ = lean_nat_mul(v___x_1872_, v_size_1866_);
v___x_1874_ = lean_nat_dec_lt(v___x_1873_, v_size_1867_);
lean_dec(v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
lean_dec(v_r_1871_);
v___x_1875_ = lean_nat_add(v___x_1865_, v_size_1867_);
v___x_1876_ = lean_nat_add(v___x_1875_, v_size_1866_);
lean_dec(v_size_1866_);
lean_dec(v___x_1875_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_impl_1864_);
lean_ctor_set(v___x_1376_, 0, v___x_1876_);
v___x_1878_ = v___x_1376_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1879_, 3, v_l_1373_);
lean_ctor_set(v_reuseFailAlloc_1879_, 4, v_impl_1864_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
else
{
lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1945_; 
lean_inc(v_l_1870_);
lean_inc(v_v_1869_);
lean_inc(v_k_1868_);
lean_inc(v_size_1867_);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_l_1373_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; lean_object* v_unused_1947_; lean_object* v_unused_1948_; lean_object* v_unused_1949_; lean_object* v_unused_1950_; 
v_unused_1946_ = lean_ctor_get(v_l_1373_, 4);
lean_dec(v_unused_1946_);
v_unused_1947_ = lean_ctor_get(v_l_1373_, 3);
lean_dec(v_unused_1947_);
v_unused_1948_ = lean_ctor_get(v_l_1373_, 2);
lean_dec(v_unused_1948_);
v_unused_1949_ = lean_ctor_get(v_l_1373_, 1);
lean_dec(v_unused_1949_);
v_unused_1950_ = lean_ctor_get(v_l_1373_, 0);
lean_dec(v_unused_1950_);
v___x_1881_ = v_l_1373_;
v_isShared_1882_ = v_isSharedCheck_1945_;
goto v_resetjp_1880_;
}
else
{
lean_dec(v_l_1373_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1945_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v_size_1883_; lean_object* v_size_1884_; lean_object* v_k_1885_; lean_object* v_v_1886_; lean_object* v_l_1887_; lean_object* v_r_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v_size_1883_ = lean_ctor_get(v_l_1870_, 0);
v_size_1884_ = lean_ctor_get(v_r_1871_, 0);
v_k_1885_ = lean_ctor_get(v_r_1871_, 1);
v_v_1886_ = lean_ctor_get(v_r_1871_, 2);
v_l_1887_ = lean_ctor_get(v_r_1871_, 3);
v_r_1888_ = lean_ctor_get(v_r_1871_, 4);
v___x_1889_ = lean_unsigned_to_nat(2u);
v___x_1890_ = lean_nat_mul(v___x_1889_, v_size_1883_);
v___x_1891_ = lean_nat_dec_lt(v_size_1884_, v___x_1890_);
lean_dec(v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1920_; 
lean_inc(v_r_1888_);
lean_inc(v_l_1887_);
lean_inc(v_v_1886_);
lean_inc(v_k_1885_);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_r_1871_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; lean_object* v_unused_1922_; lean_object* v_unused_1923_; lean_object* v_unused_1924_; lean_object* v_unused_1925_; 
v_unused_1921_ = lean_ctor_get(v_r_1871_, 4);
lean_dec(v_unused_1921_);
v_unused_1922_ = lean_ctor_get(v_r_1871_, 3);
lean_dec(v_unused_1922_);
v_unused_1923_ = lean_ctor_get(v_r_1871_, 2);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_r_1871_, 1);
lean_dec(v_unused_1924_);
v_unused_1925_ = lean_ctor_get(v_r_1871_, 0);
lean_dec(v_unused_1925_);
v___x_1893_ = v_r_1871_;
v_isShared_1894_ = v_isSharedCheck_1920_;
goto v_resetjp_1892_;
}
else
{
lean_dec(v_r_1871_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1920_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___x_1908_; lean_object* v___y_1910_; 
v___x_1895_ = lean_nat_add(v___x_1865_, v_size_1867_);
lean_dec(v_size_1867_);
v___x_1896_ = lean_nat_add(v___x_1895_, v_size_1866_);
lean_dec(v___x_1895_);
v___x_1908_ = lean_nat_add(v___x_1865_, v_size_1883_);
if (lean_obj_tag(v_l_1887_) == 0)
{
lean_object* v_size_1918_; 
v_size_1918_ = lean_ctor_get(v_l_1887_, 0);
lean_inc(v_size_1918_);
v___y_1910_ = v_size_1918_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_unsigned_to_nat(0u);
v___y_1910_ = v___x_1919_;
goto v___jp_1909_;
}
v___jp_1897_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_nat_add(v___y_1898_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec(v___y_1898_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 4, v_impl_1864_);
lean_ctor_set(v___x_1893_, 3, v_r_1888_);
lean_ctor_set(v___x_1893_, 2, v_v_1372_);
lean_ctor_set(v___x_1893_, 1, v_k_1371_);
lean_ctor_set(v___x_1893_, 0, v___x_1901_);
v___x_1903_ = v___x_1893_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1907_, 3, v_r_1888_);
lean_ctor_set(v_reuseFailAlloc_1907_, 4, v_impl_1864_);
v___x_1903_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 4, v___x_1903_);
lean_ctor_set(v___x_1881_, 3, v___y_1899_);
lean_ctor_set(v___x_1881_, 2, v_v_1886_);
lean_ctor_set(v___x_1881_, 1, v_k_1885_);
lean_ctor_set(v___x_1881_, 0, v___x_1896_);
v___x_1905_ = v___x_1881_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_k_1885_);
lean_ctor_set(v_reuseFailAlloc_1906_, 2, v_v_1886_);
lean_ctor_set(v_reuseFailAlloc_1906_, 3, v___y_1899_);
lean_ctor_set(v_reuseFailAlloc_1906_, 4, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
v___jp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1911_ = lean_nat_add(v___x_1908_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec(v___x_1908_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_l_1887_);
lean_ctor_set(v___x_1376_, 3, v_l_1870_);
lean_ctor_set(v___x_1376_, 2, v_v_1869_);
lean_ctor_set(v___x_1376_, 1, v_k_1868_);
lean_ctor_set(v___x_1376_, 0, v___x_1911_);
v___x_1913_ = v___x_1376_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_k_1868_);
lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_v_1869_);
lean_ctor_set(v_reuseFailAlloc_1917_, 3, v_l_1870_);
lean_ctor_set(v_reuseFailAlloc_1917_, 4, v_l_1887_);
v___x_1913_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_nat_add(v___x_1865_, v_size_1866_);
lean_dec(v_size_1866_);
if (lean_obj_tag(v_r_1888_) == 0)
{
lean_object* v_size_1915_; 
v_size_1915_ = lean_ctor_get(v_r_1888_, 0);
lean_inc(v_size_1915_);
v___y_1898_ = v___x_1914_;
v___y_1899_ = v___x_1913_;
v___y_1900_ = v_size_1915_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_unsigned_to_nat(0u);
v___y_1898_ = v___x_1914_;
v___y_1899_ = v___x_1913_;
v___y_1900_ = v___x_1916_;
goto v___jp_1897_;
}
}
}
}
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
lean_del_object(v___x_1376_);
v___x_1926_ = lean_nat_add(v___x_1865_, v_size_1867_);
lean_dec(v_size_1867_);
v___x_1927_ = lean_nat_add(v___x_1926_, v_size_1866_);
lean_dec(v___x_1926_);
v___x_1928_ = lean_nat_add(v___x_1865_, v_size_1866_);
lean_dec(v_size_1866_);
v___x_1929_ = lean_nat_add(v___x_1928_, v_size_1884_);
lean_dec(v___x_1928_);
lean_inc_ref(v_impl_1864_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 4, v_impl_1864_);
lean_ctor_set(v___x_1881_, 3, v_r_1871_);
lean_ctor_set(v___x_1881_, 2, v_v_1372_);
lean_ctor_set(v___x_1881_, 1, v_k_1371_);
lean_ctor_set(v___x_1881_, 0, v___x_1929_);
v___x_1931_ = v___x_1881_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1944_, 3, v_r_1871_);
lean_ctor_set(v_reuseFailAlloc_1944_, 4, v_impl_1864_);
v___x_1931_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
v_isSharedCheck_1938_ = !lean_is_exclusive(v_impl_1864_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; lean_object* v_unused_1940_; lean_object* v_unused_1941_; lean_object* v_unused_1942_; lean_object* v_unused_1943_; 
v_unused_1939_ = lean_ctor_get(v_impl_1864_, 4);
lean_dec(v_unused_1939_);
v_unused_1940_ = lean_ctor_get(v_impl_1864_, 3);
lean_dec(v_unused_1940_);
v_unused_1941_ = lean_ctor_get(v_impl_1864_, 2);
lean_dec(v_unused_1941_);
v_unused_1942_ = lean_ctor_get(v_impl_1864_, 1);
lean_dec(v_unused_1942_);
v_unused_1943_ = lean_ctor_get(v_impl_1864_, 0);
lean_dec(v_unused_1943_);
v___x_1933_ = v_impl_1864_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_dec(v_impl_1864_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 4, v___x_1931_);
lean_ctor_set(v___x_1933_, 3, v_l_1870_);
lean_ctor_set(v___x_1933_, 2, v_v_1869_);
lean_ctor_set(v___x_1933_, 1, v_k_1868_);
lean_ctor_set(v___x_1933_, 0, v___x_1927_);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_k_1868_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_v_1869_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v_l_1870_);
lean_ctor_set(v_reuseFailAlloc_1937_, 4, v___x_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v_size_1951_ = lean_ctor_get(v_impl_1864_, 0);
lean_inc(v_size_1951_);
v___x_1952_ = lean_nat_add(v___x_1865_, v_size_1951_);
lean_dec(v_size_1951_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_impl_1864_);
lean_ctor_set(v___x_1376_, 0, v___x_1952_);
v___x_1954_ = v___x_1376_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1955_, 3, v_l_1373_);
lean_ctor_set(v_reuseFailAlloc_1955_, 4, v_impl_1864_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
if (lean_obj_tag(v_l_1373_) == 0)
{
lean_object* v_l_1956_; 
v_l_1956_ = lean_ctor_get(v_l_1373_, 3);
if (lean_obj_tag(v_l_1956_) == 0)
{
lean_object* v_r_1957_; 
lean_inc_ref(v_l_1956_);
v_r_1957_ = lean_ctor_get(v_l_1373_, 4);
lean_inc(v_r_1957_);
if (lean_obj_tag(v_r_1957_) == 0)
{
lean_object* v_size_1958_; lean_object* v_k_1959_; lean_object* v_v_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1973_; 
v_size_1958_ = lean_ctor_get(v_l_1373_, 0);
v_k_1959_ = lean_ctor_get(v_l_1373_, 1);
v_v_1960_ = lean_ctor_get(v_l_1373_, 2);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_l_1373_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; lean_object* v_unused_1975_; 
v_unused_1974_ = lean_ctor_get(v_l_1373_, 4);
lean_dec(v_unused_1974_);
v_unused_1975_ = lean_ctor_get(v_l_1373_, 3);
lean_dec(v_unused_1975_);
v___x_1962_ = v_l_1373_;
v_isShared_1963_ = v_isSharedCheck_1973_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_v_1960_);
lean_inc(v_k_1959_);
lean_inc(v_size_1958_);
lean_dec(v_l_1373_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1973_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_size_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v_size_1964_ = lean_ctor_get(v_r_1957_, 0);
v___x_1965_ = lean_nat_add(v___x_1865_, v_size_1958_);
lean_dec(v_size_1958_);
v___x_1966_ = lean_nat_add(v___x_1865_, v_size_1964_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v_impl_1864_);
lean_ctor_set(v___x_1962_, 3, v_r_1957_);
lean_ctor_set(v___x_1962_, 2, v_v_1372_);
lean_ctor_set(v___x_1962_, 1, v_k_1371_);
lean_ctor_set(v___x_1962_, 0, v___x_1966_);
v___x_1968_ = v___x_1962_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_r_1957_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v_impl_1864_);
v___x_1968_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1970_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v___x_1968_);
lean_ctor_set(v___x_1376_, 3, v_l_1956_);
lean_ctor_set(v___x_1376_, 2, v_v_1960_);
lean_ctor_set(v___x_1376_, 1, v_k_1959_);
lean_ctor_set(v___x_1376_, 0, v___x_1965_);
v___x_1970_ = v___x_1376_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_k_1959_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_v_1960_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_l_1956_);
lean_ctor_set(v_reuseFailAlloc_1971_, 4, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_object* v_k_1976_; lean_object* v_v_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1988_; 
v_k_1976_ = lean_ctor_get(v_l_1373_, 1);
v_v_1977_ = lean_ctor_get(v_l_1373_, 2);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_l_1373_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; lean_object* v_unused_1990_; lean_object* v_unused_1991_; 
v_unused_1989_ = lean_ctor_get(v_l_1373_, 4);
lean_dec(v_unused_1989_);
v_unused_1990_ = lean_ctor_get(v_l_1373_, 3);
lean_dec(v_unused_1990_);
v_unused_1991_ = lean_ctor_get(v_l_1373_, 0);
lean_dec(v_unused_1991_);
v___x_1979_ = v_l_1373_;
v_isShared_1980_ = v_isSharedCheck_1988_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_v_1977_);
lean_inc(v_k_1976_);
lean_dec(v_l_1373_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1988_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1981_ = lean_unsigned_to_nat(3u);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 3, v_r_1957_);
lean_ctor_set(v___x_1979_, 2, v_v_1372_);
lean_ctor_set(v___x_1979_, 1, v_k_1371_);
lean_ctor_set(v___x_1979_, 0, v___x_1865_);
v___x_1983_ = v___x_1979_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v_r_1957_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v_r_1957_);
v___x_1983_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1985_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v___x_1983_);
lean_ctor_set(v___x_1376_, 3, v_l_1956_);
lean_ctor_set(v___x_1376_, 2, v_v_1977_);
lean_ctor_set(v___x_1376_, 1, v_k_1976_);
lean_ctor_set(v___x_1376_, 0, v___x_1981_);
v___x_1985_ = v___x_1376_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1981_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_k_1976_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_v_1977_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_l_1956_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
else
{
lean_object* v_r_1992_; 
v_r_1992_ = lean_ctor_get(v_l_1373_, 4);
lean_inc(v_r_1992_);
if (lean_obj_tag(v_r_1992_) == 0)
{
lean_object* v_k_1993_; lean_object* v_v_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2017_; 
lean_inc(v_l_1956_);
v_k_1993_ = lean_ctor_get(v_l_1373_, 1);
v_v_1994_ = lean_ctor_get(v_l_1373_, 2);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_l_1373_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; lean_object* v_unused_2019_; lean_object* v_unused_2020_; 
v_unused_2018_ = lean_ctor_get(v_l_1373_, 4);
lean_dec(v_unused_2018_);
v_unused_2019_ = lean_ctor_get(v_l_1373_, 3);
lean_dec(v_unused_2019_);
v_unused_2020_ = lean_ctor_get(v_l_1373_, 0);
lean_dec(v_unused_2020_);
v___x_1996_ = v_l_1373_;
v_isShared_1997_ = v_isSharedCheck_2017_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_v_1994_);
lean_inc(v_k_1993_);
lean_dec(v_l_1373_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2017_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_k_1998_; lean_object* v_v_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2013_; 
v_k_1998_ = lean_ctor_get(v_r_1992_, 1);
v_v_1999_ = lean_ctor_get(v_r_1992_, 2);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_r_1992_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; lean_object* v_unused_2015_; lean_object* v_unused_2016_; 
v_unused_2014_ = lean_ctor_get(v_r_1992_, 4);
lean_dec(v_unused_2014_);
v_unused_2015_ = lean_ctor_get(v_r_1992_, 3);
lean_dec(v_unused_2015_);
v_unused_2016_ = lean_ctor_get(v_r_1992_, 0);
lean_dec(v_unused_2016_);
v___x_2001_ = v_r_1992_;
v_isShared_2002_ = v_isSharedCheck_2013_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_v_1999_);
lean_inc(v_k_1998_);
lean_dec(v_r_1992_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2013_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_unsigned_to_nat(3u);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v_l_1956_);
lean_ctor_set(v___x_2001_, 3, v_l_1956_);
lean_ctor_set(v___x_2001_, 2, v_v_1994_);
lean_ctor_set(v___x_2001_, 1, v_k_1993_);
lean_ctor_set(v___x_2001_, 0, v___x_1865_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_k_1993_);
lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_v_1994_);
lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_l_1956_);
lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_l_1956_);
v___x_2005_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 4, v_l_1956_);
lean_ctor_set(v___x_1996_, 2, v_v_1372_);
lean_ctor_set(v___x_1996_, 1, v_k_1371_);
lean_ctor_set(v___x_1996_, 0, v___x_1865_);
v___x_2007_ = v___x_1996_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_2011_, 3, v_l_1956_);
lean_ctor_set(v_reuseFailAlloc_2011_, 4, v_l_1956_);
v___x_2007_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2009_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v___x_2007_);
lean_ctor_set(v___x_1376_, 3, v___x_2005_);
lean_ctor_set(v___x_1376_, 2, v_v_1999_);
lean_ctor_set(v___x_1376_, 1, v_k_1998_);
lean_ctor_set(v___x_1376_, 0, v___x_2003_);
v___x_2009_ = v___x_1376_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_k_1998_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_v_1999_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2010_, 4, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_unsigned_to_nat(2u);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_r_1992_);
lean_ctor_set(v___x_1376_, 0, v___x_2021_);
v___x_2023_ = v___x_1376_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_2024_, 3, v_l_1373_);
lean_ctor_set(v_reuseFailAlloc_2024_, 4, v_r_1992_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v___x_2026_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_l_1373_);
lean_ctor_set(v___x_1376_, 0, v___x_1865_);
v___x_2026_ = v___x_1376_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v_l_1373_);
lean_ctor_set(v_reuseFailAlloc_2027_, 4, v_l_1373_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
}
else
{
return v_t_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2030_, lean_object* v_t_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2030_, v_t_2031_);
lean_dec(v_k_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2033_, lean_object* v_v_2034_, lean_object* v_i_2035_){
_start:
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = lean_array_get_size(v_xs_2033_);
v___x_2037_ = lean_nat_dec_lt(v_i_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; 
lean_dec(v_i_2035_);
v___x_2038_ = lean_box(0);
return v___x_2038_;
}
else
{
lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = lean_array_fget_borrowed(v_xs_2033_, v_i_2035_);
v___x_2040_ = l_Lean_instBEqFVarId_beq(v___x_2039_, v_v_2034_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_unsigned_to_nat(1u);
v___x_2042_ = lean_nat_add(v_i_2035_, v___x_2041_);
lean_dec(v_i_2035_);
v_i_2035_ = v___x_2042_;
goto _start;
}
else
{
lean_object* v___x_2044_; 
v___x_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2044_, 0, v_i_2035_);
return v___x_2044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2045_, lean_object* v_v_2046_, lean_object* v_i_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2045_, v_v_2046_, v_i_2047_);
lean_dec(v_v_2046_);
lean_dec_ref(v_xs_2045_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2049_, lean_object* v_v_2050_){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2049_, v_v_2050_, v___x_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2053_, lean_object* v_v_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2053_, v_v_2054_);
lean_dec(v_v_2054_);
lean_dec_ref(v_xs_2053_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2056_, size_t v_x_2057_, lean_object* v_x_2058_){
_start:
{
if (lean_obj_tag(v_x_2056_) == 0)
{
lean_object* v_es_2059_; lean_object* v___x_2060_; size_t v___x_2061_; size_t v___x_2062_; lean_object* v_j_2063_; lean_object* v_entry_2064_; 
v_es_2059_ = lean_ctor_get(v_x_2056_, 0);
v___x_2060_ = lean_box(2);
v___x_2061_ = ((size_t)31ULL);
v___x_2062_ = lean_usize_land(v_x_2057_, v___x_2061_);
v_j_2063_ = lean_usize_to_nat(v___x_2062_);
v_entry_2064_ = lean_array_get(v___x_2060_, v_es_2059_, v_j_2063_);
switch(lean_obj_tag(v_entry_2064_))
{
case 0:
{
lean_object* v_key_2065_; uint8_t v___x_2066_; 
v_key_2065_ = lean_ctor_get(v_entry_2064_, 0);
lean_inc(v_key_2065_);
lean_dec_ref_known(v_entry_2064_, 2);
v___x_2066_ = l_Lean_instBEqFVarId_beq(v_x_2058_, v_key_2065_);
lean_dec(v_key_2065_);
if (v___x_2066_ == 0)
{
lean_dec(v_j_2063_);
return v_x_2056_;
}
else
{
lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2074_; 
lean_inc_ref(v_es_2059_);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_x_2056_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v_x_2056_, 0);
lean_dec(v_unused_2075_);
v___x_2068_ = v_x_2056_;
v_isShared_2069_ = v_isSharedCheck_2074_;
goto v_resetjp_2067_;
}
else
{
lean_dec(v_x_2056_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2074_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_array_set(v_es_2059_, v_j_2063_, v___x_2060_);
lean_dec(v_j_2063_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2070_);
v___x_2072_ = v___x_2068_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
case 1:
{
lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2110_; 
lean_inc_ref(v_es_2059_);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_x_2056_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v_x_2056_, 0);
lean_dec(v_unused_2111_);
v___x_2077_ = v_x_2056_;
v_isShared_2078_ = v_isSharedCheck_2110_;
goto v_resetjp_2076_;
}
else
{
lean_dec(v_x_2056_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2110_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_node_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2109_; 
v_node_2079_ = lean_ctor_get(v_entry_2064_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_entry_2064_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2081_ = v_entry_2064_;
v_isShared_2082_ = v_isSharedCheck_2109_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_node_2079_);
lean_dec(v_entry_2064_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2109_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
size_t v___x_2083_; lean_object* v_entries_2084_; size_t v___x_2085_; lean_object* v_newNode_2086_; lean_object* v___x_2087_; 
v___x_2083_ = ((size_t)5ULL);
v_entries_2084_ = lean_array_set(v_es_2059_, v_j_2063_, v___x_2060_);
v___x_2085_ = lean_usize_shift_right(v_x_2057_, v___x_2083_);
v_newNode_2086_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2079_, v___x_2085_, v_x_2058_);
lean_inc_ref(v_newNode_2086_);
v___x_2087_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2086_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2089_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v_newNode_2086_);
v___x_2089_ = v___x_2081_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_newNode_2086_);
v___x_2089_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = lean_array_set(v_entries_2084_, v_j_2063_, v___x_2089_);
lean_dec(v_j_2063_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2090_);
v___x_2092_ = v___x_2077_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_object* v_val_2095_; lean_object* v_fst_2096_; lean_object* v_snd_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref(v_newNode_2086_);
lean_del_object(v___x_2081_);
v_val_2095_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v___x_2087_, 1);
v_fst_2096_ = lean_ctor_get(v_val_2095_, 0);
v_snd_2097_ = lean_ctor_get(v_val_2095_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_val_2095_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2099_ = v_val_2095_;
v_isShared_2100_ = v_isSharedCheck_2108_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_snd_2097_);
lean_inc(v_fst_2096_);
lean_dec(v_val_2095_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2108_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_fst_2096_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_snd_2097_);
v___x_2102_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = lean_array_set(v_entries_2084_, v_j_2063_, v___x_2102_);
lean_dec(v_j_2063_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2103_);
v___x_2105_ = v___x_2077_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2063_);
return v_x_2056_;
}
}
}
else
{
lean_object* v_ks_2112_; lean_object* v_vs_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2127_; 
v_ks_2112_ = lean_ctor_get(v_x_2056_, 0);
v_vs_2113_ = lean_ctor_get(v_x_2056_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_x_2056_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2115_ = v_x_2056_;
v_isShared_2116_ = v_isSharedCheck_2127_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_vs_2113_);
lean_inc(v_ks_2112_);
lean_dec(v_x_2056_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2127_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2112_, v_x_2058_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2119_; 
if (v_isShared_2116_ == 0)
{
v___x_2119_ = v___x_2115_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_ks_2112_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_vs_2113_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
else
{
lean_object* v_val_2121_; lean_object* v_keys_x27_2122_; lean_object* v_vals_x27_2123_; lean_object* v___x_2125_; 
v_val_2121_ = lean_ctor_get(v___x_2117_, 0);
lean_inc_n(v_val_2121_, 2);
lean_dec_ref_known(v___x_2117_, 1);
v_keys_x27_2122_ = l_Array_eraseIdx___redArg(v_ks_2112_, v_val_2121_);
v_vals_x27_2123_ = l_Array_eraseIdx___redArg(v_vs_2113_, v_val_2121_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 1, v_vals_x27_2123_);
lean_ctor_set(v___x_2115_, 0, v_keys_x27_2122_);
v___x_2125_ = v___x_2115_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_keys_x27_2122_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_vals_x27_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2128_, lean_object* v_x_2129_, lean_object* v_x_2130_){
_start:
{
size_t v_x_2685__boxed_2131_; lean_object* v_res_2132_; 
v_x_2685__boxed_2131_ = lean_unbox_usize(v_x_2129_);
lean_dec(v_x_2129_);
v_res_2132_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2128_, v_x_2685__boxed_2131_, v_x_2130_);
lean_dec(v_x_2130_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2133_, lean_object* v_x_2134_){
_start:
{
uint64_t v___x_2135_; size_t v_h_2136_; lean_object* v___x_2137_; 
v___x_2135_ = l_Lean_instHashableFVarId_hash(v_x_2134_);
v_h_2136_ = lean_uint64_to_usize(v___x_2135_);
v___x_2137_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2133_, v_h_2136_, v_x_2134_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2138_, lean_object* v_x_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2138_, v_x_2139_);
lean_dec(v_x_2139_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object* v_lctx_2141_, lean_object* v_fvarId_2142_){
_start:
{
lean_object* v_fvarIdToDecl_2143_; lean_object* v_decls_2144_; lean_object* v_auxDeclToFullName_2145_; lean_object* v___x_2146_; 
v_fvarIdToDecl_2143_ = lean_ctor_get(v_lctx_2141_, 0);
v_decls_2144_ = lean_ctor_get(v_lctx_2141_, 1);
v_auxDeclToFullName_2145_ = lean_ctor_get(v_lctx_2141_, 2);
v___x_2146_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2143_, v_fvarId_2142_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_dec(v_fvarId_2142_);
return v_lctx_2141_;
}
else
{
lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2166_; 
lean_inc(v_auxDeclToFullName_2145_);
lean_inc_ref(v_decls_2144_);
lean_inc_ref(v_fvarIdToDecl_2143_);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_lctx_2141_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; lean_object* v_unused_2168_; lean_object* v_unused_2169_; 
v_unused_2167_ = lean_ctor_get(v_lctx_2141_, 2);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_lctx_2141_, 1);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_lctx_2141_, 0);
lean_dec(v_unused_2169_);
v___x_2148_ = v_lctx_2141_;
v_isShared_2149_ = v_isSharedCheck_2166_;
goto v_resetjp_2147_;
}
else
{
lean_dec(v_lctx_2141_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2166_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_val_2150_; lean_object* v___x_2151_; lean_object* v___y_2153_; lean_object* v_index_2165_; 
v_val_2150_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_val_2150_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2151_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2143_, v_fvarId_2142_);
v_index_2165_ = lean_ctor_get(v_val_2150_, 0);
lean_inc(v_index_2165_);
v___y_2153_ = v_index_2165_;
goto v___jp_2152_;
v___jp_2152_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2154_ = lean_box(0);
v___x_2155_ = l_Lean_PersistentArray_set___redArg(v_decls_2144_, v___y_2153_, v___x_2154_);
lean_dec(v___y_2153_);
v___x_2156_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2155_);
v___x_2157_ = l_Lean_LocalDecl_isAuxDecl(v_val_2150_);
lean_dec(v_val_2150_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2159_; 
lean_dec(v_fvarId_2142_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v___x_2156_);
lean_ctor_set(v___x_2148_, 0, v___x_2151_);
v___x_2159_ = v___x_2148_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_auxDeclToFullName_2145_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2142_, v_auxDeclToFullName_2145_);
lean_dec(v_fvarId_2142_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 2, v___x_2161_);
lean_ctor_set(v___x_2148_, 1, v___x_2156_);
lean_ctor_set(v___x_2148_, 0, v___x_2151_);
v___x_2163_ = v___x_2148_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2171_, v_x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2174_, v_x_2175_, v_x_2176_);
lean_dec(v_x_2176_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2178_, lean_object* v_k_2179_, lean_object* v_t_2180_, lean_object* v_h_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2179_, v_t_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2183_, lean_object* v_k_2184_, lean_object* v_t_2185_, lean_object* v_h_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2183_, v_k_2184_, v_t_2185_, v_h_2186_);
lean_dec(v_k_2184_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2188_, lean_object* v_x_2189_, size_t v_x_2190_, lean_object* v_x_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2189_, v_x_2190_, v_x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_){
_start:
{
size_t v_x_2907__boxed_2197_; lean_object* v_res_2198_; 
v_x_2907__boxed_2197_ = lean_unbox_usize(v_x_2195_);
lean_dec(v_x_2195_);
v_res_2198_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2193_, v_x_2194_, v_x_2907__boxed_2197_, v_x_2196_);
lean_dec(v_x_2196_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2199_){
_start:
{
lean_object* v_decls_2200_; lean_object* v_fvarIdToDecl_2201_; lean_object* v_auxDeclToFullName_2202_; lean_object* v_size_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v_decls_2200_ = lean_ctor_get(v_lctx_2199_, 1);
v_fvarIdToDecl_2201_ = lean_ctor_get(v_lctx_2199_, 0);
v_auxDeclToFullName_2202_ = lean_ctor_get(v_lctx_2199_, 2);
v_size_2203_ = lean_ctor_get(v_decls_2200_, 2);
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = lean_nat_dec_eq(v_size_2203_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = lean_box(0);
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_nat_sub(v_size_2203_, v___x_2207_);
v___x_2209_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2206_, v_decls_2200_, v___x_2208_);
lean_dec(v___x_2208_);
if (lean_obj_tag(v___x_2209_) == 0)
{
return v_lctx_2199_;
}
else
{
lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2228_; 
lean_inc(v_auxDeclToFullName_2202_);
lean_inc_ref(v_fvarIdToDecl_2201_);
lean_inc_ref(v_decls_2200_);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_lctx_2199_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; lean_object* v_unused_2230_; lean_object* v_unused_2231_; 
v_unused_2229_ = lean_ctor_get(v_lctx_2199_, 2);
lean_dec(v_unused_2229_);
v_unused_2230_ = lean_ctor_get(v_lctx_2199_, 1);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_lctx_2199_, 0);
lean_dec(v_unused_2231_);
v___x_2211_ = v_lctx_2199_;
v_isShared_2212_ = v_isSharedCheck_2228_;
goto v_resetjp_2210_;
}
else
{
lean_dec(v_lctx_2199_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2228_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v_val_2213_; lean_object* v___y_2215_; lean_object* v_fvarId_2227_; 
v_val_2213_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_val_2213_);
lean_dec_ref_known(v___x_2209_, 1);
v_fvarId_2227_ = lean_ctor_get(v_val_2213_, 1);
lean_inc(v_fvarId_2227_);
v___y_2215_ = v_fvarId_2227_;
goto v___jp_2214_;
v___jp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2216_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2201_, v___y_2215_);
v___x_2217_ = l_Lean_PersistentArray_pop___redArg(v_decls_2200_);
v___x_2218_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2217_);
v___x_2219_ = l_Lean_LocalDecl_isAuxDecl(v_val_2213_);
lean_dec(v_val_2213_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2221_; 
lean_dec(v___y_2215_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 1, v___x_2218_);
lean_ctor_set(v___x_2211_, 0, v___x_2216_);
v___x_2221_ = v___x_2211_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_auxDeclToFullName_2202_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2215_, v_auxDeclToFullName_2202_);
lean_dec(v___y_2215_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 2, v___x_2223_);
lean_ctor_set(v___x_2211_, 1, v___x_2218_);
lean_ctor_set(v___x_2211_, 0, v___x_2216_);
v___x_2225_ = v___x_2211_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
else
{
return v_lctx_2199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2232_, lean_object* v_as_2233_, lean_object* v_i_2234_){
_start:
{
lean_object* v_zero_2235_; uint8_t v_isZero_2236_; 
v_zero_2235_ = lean_unsigned_to_nat(0u);
v_isZero_2236_ = lean_nat_dec_eq(v_i_2234_, v_zero_2235_);
if (v_isZero_2236_ == 1)
{
lean_object* v___x_2237_; 
lean_dec(v_i_2234_);
v___x_2237_ = lean_box(0);
return v___x_2237_;
}
else
{
lean_object* v_one_2238_; lean_object* v_n_2239_; lean_object* v___y_2241_; lean_object* v___x_2243_; lean_object* v___y_2245_; 
v_one_2238_ = lean_unsigned_to_nat(1u);
v_n_2239_ = lean_nat_sub(v_i_2234_, v_one_2238_);
lean_dec(v_i_2234_);
v___x_2243_ = lean_array_fget_borrowed(v_as_2233_, v_n_2239_);
if (lean_obj_tag(v___x_2243_) == 0)
{
v___y_2241_ = v___x_2243_;
goto v___jp_2240_;
}
else
{
lean_object* v_val_2248_; lean_object* v_userName_2249_; 
v_val_2248_ = lean_ctor_get(v___x_2243_, 0);
v_userName_2249_ = lean_ctor_get(v_val_2248_, 2);
v___y_2245_ = v_userName_2249_;
goto v___jp_2244_;
}
v___jp_2240_:
{
if (lean_obj_tag(v___y_2241_) == 0)
{
v_i_2234_ = v_n_2239_;
goto _start;
}
else
{
lean_dec(v_n_2239_);
lean_inc_ref(v___y_2241_);
return v___y_2241_;
}
}
v___jp_2244_:
{
uint8_t v___x_2246_; 
v___x_2246_ = lean_name_eq(v___y_2245_, v_userName_2232_);
if (v___x_2246_ == 0)
{
v_i_2234_ = v_n_2239_;
goto _start;
}
else
{
v___y_2241_ = v___x_2243_;
goto v___jp_2240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2250_, lean_object* v_as_2251_, lean_object* v_i_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2250_, v_as_2251_, v_i_2252_);
lean_dec_ref(v_as_2251_);
lean_dec(v_userName_2250_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2254_, lean_object* v_as_2255_, lean_object* v_i_2256_){
_start:
{
lean_object* v_zero_2257_; uint8_t v_isZero_2258_; 
v_zero_2257_ = lean_unsigned_to_nat(0u);
v_isZero_2258_ = lean_nat_dec_eq(v_i_2256_, v_zero_2257_);
if (v_isZero_2258_ == 1)
{
lean_object* v___x_2259_; 
lean_dec(v_i_2256_);
v___x_2259_ = lean_box(0);
return v___x_2259_;
}
else
{
lean_object* v_one_2260_; lean_object* v_n_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v_one_2260_ = lean_unsigned_to_nat(1u);
v_n_2261_ = lean_nat_sub(v_i_2256_, v_one_2260_);
lean_dec(v_i_2256_);
v___x_2262_ = lean_array_fget_borrowed(v_as_2255_, v_n_2261_);
v___x_2263_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2254_, v___x_2262_);
if (lean_obj_tag(v___x_2263_) == 0)
{
v_i_2256_ = v_n_2261_;
goto _start;
}
else
{
lean_dec(v_n_2261_);
return v___x_2263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2265_, lean_object* v_x_2266_){
_start:
{
if (lean_obj_tag(v_x_2266_) == 0)
{
lean_object* v_cs_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v_cs_2267_ = lean_ctor_get(v_x_2266_, 0);
v___x_2268_ = lean_array_get_size(v_cs_2267_);
v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2265_, v_cs_2267_, v___x_2268_);
return v___x_2269_;
}
else
{
lean_object* v_vs_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_vs_2270_ = lean_ctor_get(v_x_2266_, 0);
v___x_2271_ = lean_array_get_size(v_vs_2270_);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2265_, v_vs_2270_, v___x_2271_);
return v___x_2272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2273_, lean_object* v_x_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2273_, v_x_2274_);
lean_dec_ref(v_x_2274_);
lean_dec(v_userName_2273_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2276_, lean_object* v_as_2277_, lean_object* v_i_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2276_, v_as_2277_, v_i_2278_);
lean_dec_ref(v_as_2277_);
lean_dec(v_userName_2276_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2280_, lean_object* v_t_2281_){
_start:
{
lean_object* v_root_2282_; lean_object* v_tail_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_root_2282_ = lean_ctor_get(v_t_2281_, 0);
v_tail_2283_ = lean_ctor_get(v_t_2281_, 1);
v___x_2284_ = lean_array_get_size(v_tail_2283_);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2280_, v_tail_2283_, v___x_2284_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2280_, v_root_2282_);
return v___x_2286_;
}
else
{
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2287_, lean_object* v_t_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2287_, v_t_2288_);
lean_dec_ref(v_t_2288_);
lean_dec(v_userName_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2290_, lean_object* v_userName_2291_){
_start:
{
lean_object* v_decls_2292_; lean_object* v___x_2293_; 
v_decls_2292_ = lean_ctor_get(v_lctx_2290_, 1);
v___x_2293_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2291_, v_decls_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2294_, lean_object* v_userName_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2294_, v_userName_2295_);
lean_dec(v_userName_2295_);
lean_dec_ref(v_lctx_2294_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2297_, lean_object* v_as_2298_, lean_object* v_i_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2297_, v_as_2298_, v_i_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2302_, lean_object* v_as_2303_, lean_object* v_i_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2302_, v_as_2303_, v_i_2304_, v_a_2305_);
lean_dec_ref(v_as_2303_);
lean_dec(v_userName_2302_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2307_, lean_object* v_as_2308_, lean_object* v_i_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2307_, v_as_2308_, v_i_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2312_, lean_object* v_as_2313_, lean_object* v_i_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2312_, v_as_2313_, v_i_2314_, v_a_2315_);
lean_dec_ref(v_as_2313_);
lean_dec(v_userName_2312_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2320_, lean_object* v_userName_2321_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2320_, v_userName_2321_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2323_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2324_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2325_ = lean_unsigned_to_nat(403u);
v___x_2326_ = lean_unsigned_to_nat(17u);
v___x_2327_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2328_ = 1;
v___x_2329_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2321_, v___x_2328_);
v___x_2330_ = lean_string_append(v___x_2327_, v___x_2329_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2332_ = lean_string_append(v___x_2330_, v___x_2331_);
v___x_2333_ = l_mkPanicMessageWithDecl(v___x_2323_, v___x_2324_, v___x_2325_, v___x_2326_, v___x_2332_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2333_);
return v___x_2334_;
}
else
{
lean_object* v_val_2335_; 
lean_dec(v_userName_2321_);
v_val_2335_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_val_2335_);
lean_dec_ref_known(v___x_2322_, 1);
return v_val_2335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2336_, lean_object* v_userName_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2336_, v_userName_2337_);
lean_dec_ref(v_lctx_2336_);
return v_res_2338_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2339_, lean_object* v_userName_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2339_, v_userName_2340_);
if (lean_obj_tag(v___x_2341_) == 0)
{
uint8_t v___x_2342_; 
v___x_2342_ = 0;
return v___x_2342_;
}
else
{
uint8_t v___x_2343_; 
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = 1;
return v___x_2343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2344_, lean_object* v_userName_2345_){
_start:
{
uint8_t v_res_2346_; lean_object* v_r_2347_; 
v_res_2346_ = l_Lean_LocalContext_usesUserName(v_lctx_2344_, v_userName_2345_);
lean_dec(v_userName_2345_);
lean_dec_ref(v_lctx_2344_);
v_r_2347_ = lean_box(v_res_2346_);
return v_r_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2348_, lean_object* v_suggestion_2349_, lean_object* v_i_2350_){
_start:
{
lean_object* v_curr_2351_; uint8_t v___x_2352_; 
lean_inc(v_i_2350_);
lean_inc(v_suggestion_2349_);
v_curr_2351_ = lean_name_append_index_after(v_suggestion_2349_, v_i_2350_);
v___x_2352_ = l_Lean_LocalContext_usesUserName(v_lctx_2348_, v_curr_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_dec(v_suggestion_2349_);
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = lean_nat_add(v_i_2350_, v___x_2353_);
lean_dec(v_i_2350_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v_curr_2351_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
return v___x_2355_;
}
else
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
lean_dec(v_curr_2351_);
v___x_2356_ = lean_unsigned_to_nat(1u);
v___x_2357_ = lean_nat_add(v_i_2350_, v___x_2356_);
lean_dec(v_i_2350_);
v_i_2350_ = v___x_2357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2359_, lean_object* v_suggestion_2360_, lean_object* v_i_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2359_, v_suggestion_2360_, v_i_2361_);
lean_dec_ref(v_lctx_2359_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2363_, lean_object* v_suggestion_2364_){
_start:
{
lean_object* v_suggestion_2365_; uint8_t v___x_2366_; 
v_suggestion_2365_ = l_Lean_Name_eraseMacroScopes(v_suggestion_2364_);
v___x_2366_ = l_Lean_LocalContext_usesUserName(v_lctx_2363_, v_suggestion_2365_);
if (v___x_2366_ == 0)
{
return v_suggestion_2365_;
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v_fst_2369_; 
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2363_, v_suggestion_2365_, v___x_2367_);
v_fst_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_fst_2369_);
lean_dec_ref(v___x_2368_);
return v_fst_2369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2370_, lean_object* v_suggestion_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_LocalContext_getUnusedName(v_lctx_2370_, v_suggestion_2371_);
lean_dec(v_suggestion_2371_);
lean_dec_ref(v_lctx_2370_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2373_){
_start:
{
lean_object* v_decls_2374_; lean_object* v_size_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
v_decls_2374_ = lean_ctor_get(v_lctx_2373_, 1);
v_size_2375_ = lean_ctor_get(v_decls_2374_, 2);
v___x_2376_ = lean_box(0);
v___x_2377_ = lean_unsigned_to_nat(1u);
v___x_2378_ = lean_nat_sub(v_size_2375_, v___x_2377_);
v___x_2379_ = lean_nat_dec_lt(v___x_2378_, v_size_2375_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
lean_dec(v___x_2378_);
v___x_2380_ = l_outOfBounds___redArg(v___x_2376_);
return v___x_2380_;
}
else
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2376_, v_decls_2374_, v___x_2378_);
lean_dec(v___x_2378_);
return v___x_2381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object* v_lctx_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_LocalContext_lastDecl(v_lctx_2382_);
lean_dec_ref(v_lctx_2382_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2384_, lean_object* v_fvarId_2385_, lean_object* v_userName_2386_){
_start:
{
lean_object* v_fvarIdToDecl_2387_; lean_object* v_decls_2388_; lean_object* v_auxDeclToFullName_2389_; lean_object* v_decl_2390_; lean_object* v_decl_2391_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2399_; lean_object* v_fvarId_2402_; 
v_fvarIdToDecl_2387_ = lean_ctor_get(v_lctx_2384_, 0);
lean_inc_ref(v_fvarIdToDecl_2387_);
v_decls_2388_ = lean_ctor_get(v_lctx_2384_, 1);
lean_inc_ref(v_decls_2388_);
v_auxDeclToFullName_2389_ = lean_ctor_get(v_lctx_2384_, 2);
lean_inc(v_auxDeclToFullName_2389_);
v_decl_2390_ = l_Lean_LocalContext_get_x21(v_lctx_2384_, v_fvarId_2385_);
v_decl_2391_ = l_Lean_LocalDecl_setUserName(v_decl_2390_, v_userName_2386_);
v_fvarId_2402_ = lean_ctor_get(v_decl_2391_, 1);
lean_inc(v_fvarId_2402_);
v___y_2399_ = v_fvarId_2402_;
goto v___jp_2398_;
v___jp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2395_, 0, v_decl_2391_);
v___x_2396_ = l_Lean_PersistentArray_set___redArg(v_decls_2388_, v___y_2394_, v___x_2395_);
lean_dec(v___y_2394_);
v___x_2397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2397_, 0, v___y_2393_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
lean_ctor_set(v___x_2397_, 2, v_auxDeclToFullName_2389_);
return v___x_2397_;
}
v___jp_2398_:
{
lean_object* v___x_2400_; lean_object* v_index_2401_; 
lean_inc_ref(v_decl_2391_);
v___x_2400_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2387_, v___y_2399_, v_decl_2391_);
v_index_2401_ = lean_ctor_get(v_decl_2391_, 0);
lean_inc(v_index_2401_);
v___y_2393_ = v___x_2400_;
v___y_2394_ = v_index_2401_;
goto v___jp_2392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2403_, lean_object* v_fromName_2404_, lean_object* v_toName_2405_){
_start:
{
lean_object* v_fvarIdToDecl_2406_; lean_object* v_decls_2407_; lean_object* v_auxDeclToFullName_2408_; lean_object* v___x_2409_; 
v_fvarIdToDecl_2406_ = lean_ctor_get(v_lctx_2403_, 0);
v_decls_2407_ = lean_ctor_get(v_lctx_2403_, 1);
v_auxDeclToFullName_2408_ = lean_ctor_get(v_lctx_2403_, 2);
v___x_2409_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2403_, v_fromName_2404_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_dec(v_toName_2405_);
return v_lctx_2403_;
}
else
{
lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2434_; 
lean_inc(v_auxDeclToFullName_2408_);
lean_inc_ref(v_decls_2407_);
lean_inc_ref(v_fvarIdToDecl_2406_);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_lctx_2403_);
if (v_isSharedCheck_2434_ == 0)
{
lean_object* v_unused_2435_; lean_object* v_unused_2436_; lean_object* v_unused_2437_; 
v_unused_2435_ = lean_ctor_get(v_lctx_2403_, 2);
lean_dec(v_unused_2435_);
v_unused_2436_ = lean_ctor_get(v_lctx_2403_, 1);
lean_dec(v_unused_2436_);
v_unused_2437_ = lean_ctor_get(v_lctx_2403_, 0);
lean_dec(v_unused_2437_);
v___x_2411_ = v_lctx_2403_;
v_isShared_2412_ = v_isSharedCheck_2434_;
goto v_resetjp_2410_;
}
else
{
lean_dec(v_lctx_2403_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2434_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v_val_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2433_; 
v_val_2413_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2415_ = v___x_2409_;
v_isShared_2416_ = v_isSharedCheck_2433_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_val_2413_);
lean_dec(v___x_2409_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2433_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v_decl_2417_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2429_; lean_object* v_fvarId_2432_; 
v_decl_2417_ = l_Lean_LocalDecl_setUserName(v_val_2413_, v_toName_2405_);
v_fvarId_2432_ = lean_ctor_get(v_decl_2417_, 1);
lean_inc(v_fvarId_2432_);
v___y_2429_ = v_fvarId_2432_;
goto v___jp_2428_;
v___jp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v_decl_2417_);
v___x_2422_ = v___x_2415_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_decl_2417_);
v___x_2422_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
v___x_2423_ = l_Lean_PersistentArray_set___redArg(v_decls_2407_, v___y_2420_, v___x_2422_);
lean_dec(v___y_2420_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 1, v___x_2423_);
lean_ctor_set(v___x_2411_, 0, v___y_2419_);
v___x_2425_ = v___x_2411_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___y_2419_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v___x_2423_);
lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_auxDeclToFullName_2408_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
v___jp_2428_:
{
lean_object* v___x_2430_; lean_object* v_index_2431_; 
lean_inc_ref(v_decl_2417_);
v___x_2430_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2406_, v___y_2429_, v_decl_2417_);
v_index_2431_ = lean_ctor_get(v_decl_2417_, 0);
lean_inc(v_index_2431_);
v___y_2419_ = v___x_2430_;
v___y_2420_ = v_index_2431_;
goto v___jp_2418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2438_, lean_object* v_fromName_2439_, lean_object* v_toName_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_LocalContext_renameUserName(v_lctx_2438_, v_fromName_2439_, v_toName_2440_);
lean_dec(v_fromName_2439_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2444_, lean_object* v_fvarId_2445_, lean_object* v_f_2446_){
_start:
{
lean_object* v_fvarIdToDecl_2447_; lean_object* v_decls_2448_; lean_object* v_auxDeclToFullName_2449_; lean_object* v___x_2450_; 
v_fvarIdToDecl_2447_ = lean_ctor_get(v_lctx_2444_, 0);
v_decls_2448_ = lean_ctor_get(v_lctx_2444_, 1);
v_auxDeclToFullName_2449_ = lean_ctor_get(v_lctx_2444_, 2);
lean_inc_ref(v_lctx_2444_);
v___x_2450_ = lean_local_ctx_find(v_lctx_2444_, v_fvarId_2445_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_dec_ref(v_f_2446_);
return v_lctx_2444_;
}
else
{
lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2477_; 
lean_inc(v_auxDeclToFullName_2449_);
lean_inc_ref(v_decls_2448_);
lean_inc_ref(v_fvarIdToDecl_2447_);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_lctx_2444_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; lean_object* v_unused_2479_; lean_object* v_unused_2480_; 
v_unused_2478_ = lean_ctor_get(v_lctx_2444_, 2);
lean_dec(v_unused_2478_);
v_unused_2479_ = lean_ctor_get(v_lctx_2444_, 1);
lean_dec(v_unused_2479_);
v_unused_2480_ = lean_ctor_get(v_lctx_2444_, 0);
lean_dec(v_unused_2480_);
v___x_2452_ = v_lctx_2444_;
v_isShared_2453_ = v_isSharedCheck_2477_;
goto v_resetjp_2451_;
}
else
{
lean_dec(v_lctx_2444_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2477_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v_val_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2476_; 
v_val_2454_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2456_ = v___x_2450_;
v_isShared_2457_ = v_isSharedCheck_2476_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_val_2454_);
lean_dec(v___x_2450_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2476_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_decl_2460_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2472_; lean_object* v_fvarId_2475_; 
v___x_2458_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2459_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2460_ = lean_apply_1(v_f_2446_, v_val_2454_);
v_fvarId_2475_ = lean_ctor_get(v_decl_2460_, 1);
lean_inc(v_fvarId_2475_);
v___y_2472_ = v_fvarId_2475_;
goto v___jp_2471_;
v___jp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v_decl_2460_);
v___x_2465_ = v___x_2456_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_decl_2460_);
v___x_2465_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2466_ = l_Lean_PersistentArray_set___redArg(v_decls_2448_, v___y_2463_, v___x_2465_);
lean_dec(v___y_2463_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2466_);
lean_ctor_set(v___x_2452_, 0, v___y_2462_);
v___x_2468_ = v___x_2452_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___y_2462_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_auxDeclToFullName_2449_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
v___jp_2471_:
{
lean_object* v___x_2473_; lean_object* v_index_2474_; 
lean_inc_ref(v_decl_2460_);
v___x_2473_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2458_, v___x_2459_, v_fvarIdToDecl_2447_, v___y_2472_, v_decl_2460_);
v_index_2474_ = lean_ctor_get(v_decl_2460_, 0);
lean_inc(v_index_2474_);
v___y_2462_ = v___x_2473_;
v___y_2463_ = v_index_2474_;
goto v___jp_2461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2481_, lean_object* v_as_2482_, size_t v_i_2483_, size_t v_stop_2484_, lean_object* v_b_2485_){
_start:
{
lean_object* v___y_2487_; uint8_t v___x_2491_; 
v___x_2491_ = lean_usize_dec_eq(v_i_2483_, v_stop_2484_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_array_uget(v_as_2482_, v_i_2483_);
if (lean_obj_tag(v___x_2492_) == 0)
{
v___y_2487_ = v_b_2485_;
goto v___jp_2486_;
}
else
{
lean_object* v_val_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2520_; 
v_val_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2520_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_val_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2520_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_fvarIdToDecl_2497_; lean_object* v_decls_2498_; lean_object* v_auxDeclToFullName_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2519_; 
v_fvarIdToDecl_2497_ = lean_ctor_get(v_b_2485_, 0);
v_decls_2498_ = lean_ctor_get(v_b_2485_, 1);
v_auxDeclToFullName_2499_ = lean_ctor_get(v_b_2485_, 2);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_b_2485_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2501_ = v_b_2485_;
v_isShared_2502_ = v_isSharedCheck_2519_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_auxDeclToFullName_2499_);
lean_inc(v_decls_2498_);
lean_inc(v_fvarIdToDecl_2497_);
lean_dec(v_b_2485_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2519_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_decl_2503_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2515_; lean_object* v_fvarId_2518_; 
lean_inc_ref(v_f_2481_);
v_decl_2503_ = lean_apply_1(v_f_2481_, v_val_2493_);
v_fvarId_2518_ = lean_ctor_get(v_decl_2503_, 1);
lean_inc(v_fvarId_2518_);
v___y_2515_ = v_fvarId_2518_;
goto v___jp_2514_;
v___jp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v_decl_2503_);
v___x_2508_ = v___x_2495_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_decl_2503_);
v___x_2508_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2509_ = l_Lean_PersistentArray_set___redArg(v_decls_2498_, v___y_2506_, v___x_2508_);
lean_dec(v___y_2506_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2509_);
lean_ctor_set(v___x_2501_, 0, v___y_2505_);
v___x_2511_ = v___x_2501_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___y_2505_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_auxDeclToFullName_2499_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
v___y_2487_ = v___x_2511_;
goto v___jp_2486_;
}
}
}
v___jp_2514_:
{
lean_object* v___x_2516_; lean_object* v_index_2517_; 
lean_inc_ref(v_decl_2503_);
v___x_2516_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2497_, v___y_2515_, v_decl_2503_);
v_index_2517_ = lean_ctor_get(v_decl_2503_, 0);
lean_inc(v_index_2517_);
v___y_2505_ = v___x_2516_;
v___y_2506_ = v_index_2517_;
goto v___jp_2504_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_2481_);
return v_b_2485_;
}
v___jp_2486_:
{
size_t v___x_2488_; size_t v___x_2489_; 
v___x_2488_ = ((size_t)1ULL);
v___x_2489_ = lean_usize_add(v_i_2483_, v___x_2488_);
v_i_2483_ = v___x_2489_;
v_b_2485_ = v___y_2487_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2521_, lean_object* v_as_2522_, lean_object* v_i_2523_, lean_object* v_stop_2524_, lean_object* v_b_2525_){
_start:
{
size_t v_i_boxed_2526_; size_t v_stop_boxed_2527_; lean_object* v_res_2528_; 
v_i_boxed_2526_ = lean_unbox_usize(v_i_2523_);
lean_dec(v_i_2523_);
v_stop_boxed_2527_ = lean_unbox_usize(v_stop_2524_);
lean_dec(v_stop_2524_);
v_res_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2521_, v_as_2522_, v_i_boxed_2526_, v_stop_boxed_2527_, v_b_2525_);
lean_dec_ref(v_as_2522_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2529_, lean_object* v_x_2530_, lean_object* v_x_2531_){
_start:
{
if (lean_obj_tag(v_x_2530_) == 0)
{
lean_object* v_cs_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v_cs_2532_ = lean_ctor_get(v_x_2530_, 0);
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = lean_array_get_size(v_cs_2532_);
v___x_2535_ = lean_nat_dec_lt(v___x_2533_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_dec_ref(v_f_2529_);
return v_x_2531_;
}
else
{
uint8_t v___x_2536_; 
v___x_2536_ = lean_nat_dec_le(v___x_2534_, v___x_2534_);
if (v___x_2536_ == 0)
{
if (v___x_2535_ == 0)
{
lean_dec_ref(v_f_2529_);
return v_x_2531_;
}
else
{
size_t v___x_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = ((size_t)0ULL);
v___x_2538_ = lean_usize_of_nat(v___x_2534_);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2529_, v_cs_2532_, v___x_2537_, v___x_2538_, v_x_2531_);
return v___x_2539_;
}
}
else
{
size_t v___x_2540_; size_t v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = ((size_t)0ULL);
v___x_2541_ = lean_usize_of_nat(v___x_2534_);
v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2529_, v_cs_2532_, v___x_2540_, v___x_2541_, v_x_2531_);
return v___x_2542_;
}
}
}
else
{
lean_object* v_vs_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v_vs_2543_ = lean_ctor_get(v_x_2530_, 0);
v___x_2544_ = lean_unsigned_to_nat(0u);
v___x_2545_ = lean_array_get_size(v_vs_2543_);
v___x_2546_ = lean_nat_dec_lt(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_dec_ref(v_f_2529_);
return v_x_2531_;
}
else
{
uint8_t v___x_2547_; 
v___x_2547_ = lean_nat_dec_le(v___x_2545_, v___x_2545_);
if (v___x_2547_ == 0)
{
if (v___x_2546_ == 0)
{
lean_dec_ref(v_f_2529_);
return v_x_2531_;
}
else
{
size_t v___x_2548_; size_t v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = ((size_t)0ULL);
v___x_2549_ = lean_usize_of_nat(v___x_2545_);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2529_, v_vs_2543_, v___x_2548_, v___x_2549_, v_x_2531_);
return v___x_2550_;
}
}
else
{
size_t v___x_2551_; size_t v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = ((size_t)0ULL);
v___x_2552_ = lean_usize_of_nat(v___x_2545_);
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2529_, v_vs_2543_, v___x_2551_, v___x_2552_, v_x_2531_);
return v___x_2553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2554_, lean_object* v_as_2555_, size_t v_i_2556_, size_t v_stop_2557_, lean_object* v_b_2558_){
_start:
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_usize_dec_eq(v_i_2556_, v_stop_2557_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2561_; size_t v___x_2562_; size_t v___x_2563_; 
v___x_2560_ = lean_array_uget_borrowed(v_as_2555_, v_i_2556_);
lean_inc_ref(v_f_2554_);
v___x_2561_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2554_, v___x_2560_, v_b_2558_);
v___x_2562_ = ((size_t)1ULL);
v___x_2563_ = lean_usize_add(v_i_2556_, v___x_2562_);
v_i_2556_ = v___x_2563_;
v_b_2558_ = v___x_2561_;
goto _start;
}
else
{
lean_dec_ref(v_f_2554_);
return v_b_2558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2565_, lean_object* v_as_2566_, lean_object* v_i_2567_, lean_object* v_stop_2568_, lean_object* v_b_2569_){
_start:
{
size_t v_i_boxed_2570_; size_t v_stop_boxed_2571_; lean_object* v_res_2572_; 
v_i_boxed_2570_ = lean_unbox_usize(v_i_2567_);
lean_dec(v_i_2567_);
v_stop_boxed_2571_ = lean_unbox_usize(v_stop_2568_);
lean_dec(v_stop_2568_);
v_res_2572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2565_, v_as_2566_, v_i_boxed_2570_, v_stop_boxed_2571_, v_b_2569_);
lean_dec_ref(v_as_2566_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2573_, lean_object* v_x_2574_, lean_object* v_x_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2573_, v_x_2574_, v_x_2575_);
lean_dec_ref(v_x_2574_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2577_, lean_object* v_x_2578_, size_t v_x_2579_, size_t v_x_2580_, lean_object* v_x_2581_){
_start:
{
if (lean_obj_tag(v_x_2578_) == 0)
{
lean_object* v_cs_2582_; lean_object* v___x_2583_; size_t v___x_2584_; lean_object* v_j_2585_; lean_object* v___x_2586_; size_t v___x_2587_; size_t v___x_2588_; size_t v___x_2589_; size_t v___x_2590_; size_t v___x_2591_; size_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v_cs_2582_ = lean_ctor_get(v_x_2578_, 0);
v___x_2583_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2584_ = lean_usize_shift_right(v_x_2579_, v_x_2580_);
v_j_2585_ = lean_usize_to_nat(v___x_2584_);
v___x_2586_ = lean_array_get_borrowed(v___x_2583_, v_cs_2582_, v_j_2585_);
v___x_2587_ = ((size_t)1ULL);
v___x_2588_ = lean_usize_shift_left(v___x_2587_, v_x_2580_);
v___x_2589_ = lean_usize_sub(v___x_2588_, v___x_2587_);
v___x_2590_ = lean_usize_land(v_x_2579_, v___x_2589_);
v___x_2591_ = ((size_t)5ULL);
v___x_2592_ = lean_usize_sub(v_x_2580_, v___x_2591_);
lean_inc_ref(v_f_2577_);
v___x_2593_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2577_, v___x_2586_, v___x_2590_, v___x_2592_, v_x_2581_);
v___x_2594_ = lean_unsigned_to_nat(1u);
v___x_2595_ = lean_nat_add(v_j_2585_, v___x_2594_);
lean_dec(v_j_2585_);
v___x_2596_ = lean_array_get_size(v_cs_2582_);
v___x_2597_ = lean_nat_dec_lt(v___x_2595_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_dec(v___x_2595_);
lean_dec_ref(v_f_2577_);
return v___x_2593_;
}
else
{
uint8_t v___x_2598_; 
v___x_2598_ = lean_nat_dec_le(v___x_2596_, v___x_2596_);
if (v___x_2598_ == 0)
{
if (v___x_2597_ == 0)
{
lean_dec(v___x_2595_);
lean_dec_ref(v_f_2577_);
return v___x_2593_;
}
else
{
size_t v___x_2599_; size_t v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = lean_usize_of_nat(v___x_2595_);
lean_dec(v___x_2595_);
v___x_2600_ = lean_usize_of_nat(v___x_2596_);
v___x_2601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2577_, v_cs_2582_, v___x_2599_, v___x_2600_, v___x_2593_);
return v___x_2601_;
}
}
else
{
size_t v___x_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_usize_of_nat(v___x_2595_);
lean_dec(v___x_2595_);
v___x_2603_ = lean_usize_of_nat(v___x_2596_);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2577_, v_cs_2582_, v___x_2602_, v___x_2603_, v___x_2593_);
return v___x_2604_;
}
}
}
else
{
lean_object* v_vs_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v_vs_2605_ = lean_ctor_get(v_x_2578_, 0);
v___x_2606_ = lean_usize_to_nat(v_x_2579_);
v___x_2607_ = lean_array_get_size(v_vs_2605_);
v___x_2608_ = lean_nat_dec_lt(v___x_2606_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_dec(v___x_2606_);
lean_dec_ref(v_f_2577_);
return v_x_2581_;
}
else
{
uint8_t v___x_2609_; 
v___x_2609_ = lean_nat_dec_le(v___x_2607_, v___x_2607_);
if (v___x_2609_ == 0)
{
if (v___x_2608_ == 0)
{
lean_dec(v___x_2606_);
lean_dec_ref(v_f_2577_);
return v_x_2581_;
}
else
{
size_t v___x_2610_; size_t v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_usize_of_nat(v___x_2606_);
lean_dec(v___x_2606_);
v___x_2611_ = lean_usize_of_nat(v___x_2607_);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2577_, v_vs_2605_, v___x_2610_, v___x_2611_, v_x_2581_);
return v___x_2612_;
}
}
else
{
size_t v___x_2613_; size_t v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = lean_usize_of_nat(v___x_2606_);
lean_dec(v___x_2606_);
v___x_2614_ = lean_usize_of_nat(v___x_2607_);
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2577_, v_vs_2605_, v___x_2613_, v___x_2614_, v_x_2581_);
return v___x_2615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2616_, lean_object* v_x_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_){
_start:
{
size_t v_x_1859__boxed_2621_; size_t v_x_1860__boxed_2622_; lean_object* v_res_2623_; 
v_x_1859__boxed_2621_ = lean_unbox_usize(v_x_2618_);
lean_dec(v_x_2618_);
v_x_1860__boxed_2622_ = lean_unbox_usize(v_x_2619_);
lean_dec(v_x_2619_);
v_res_2623_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2616_, v_x_2617_, v_x_1859__boxed_2621_, v_x_1860__boxed_2622_, v_x_2620_);
lean_dec_ref(v_x_2617_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2624_, lean_object* v_t_2625_, lean_object* v_init_2626_, lean_object* v_start_2627_){
_start:
{
lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = lean_nat_dec_eq(v_start_2627_, v___x_2628_);
if (v___x_2629_ == 0)
{
lean_object* v_root_2630_; lean_object* v_tail_2631_; size_t v_shift_2632_; lean_object* v_tailOff_2633_; uint8_t v___x_2634_; 
v_root_2630_ = lean_ctor_get(v_t_2625_, 0);
v_tail_2631_ = lean_ctor_get(v_t_2625_, 1);
v_shift_2632_ = lean_ctor_get_usize(v_t_2625_, 4);
v_tailOff_2633_ = lean_ctor_get(v_t_2625_, 3);
v___x_2634_ = lean_nat_dec_le(v_tailOff_2633_, v_start_2627_);
if (v___x_2634_ == 0)
{
size_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v___x_2635_ = lean_usize_of_nat(v_start_2627_);
lean_inc_ref(v_f_2624_);
v___x_2636_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2624_, v_root_2630_, v___x_2635_, v_shift_2632_, v_init_2626_);
v___x_2637_ = lean_array_get_size(v_tail_2631_);
v___x_2638_ = lean_nat_dec_lt(v___x_2628_, v___x_2637_);
if (v___x_2638_ == 0)
{
lean_dec_ref(v_f_2624_);
return v___x_2636_;
}
else
{
uint8_t v___x_2639_; 
v___x_2639_ = lean_nat_dec_le(v___x_2637_, v___x_2637_);
if (v___x_2639_ == 0)
{
if (v___x_2638_ == 0)
{
lean_dec_ref(v_f_2624_);
return v___x_2636_;
}
else
{
size_t v___x_2640_; size_t v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = ((size_t)0ULL);
v___x_2641_ = lean_usize_of_nat(v___x_2637_);
v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2624_, v_tail_2631_, v___x_2640_, v___x_2641_, v___x_2636_);
return v___x_2642_;
}
}
else
{
size_t v___x_2643_; size_t v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = ((size_t)0ULL);
v___x_2644_ = lean_usize_of_nat(v___x_2637_);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2624_, v_tail_2631_, v___x_2643_, v___x_2644_, v___x_2636_);
return v___x_2645_;
}
}
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2646_ = lean_nat_sub(v_start_2627_, v_tailOff_2633_);
v___x_2647_ = lean_array_get_size(v_tail_2631_);
v___x_2648_ = lean_nat_dec_lt(v___x_2646_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_dec(v___x_2646_);
lean_dec_ref(v_f_2624_);
return v_init_2626_;
}
else
{
uint8_t v___x_2649_; 
v___x_2649_ = lean_nat_dec_le(v___x_2647_, v___x_2647_);
if (v___x_2649_ == 0)
{
if (v___x_2648_ == 0)
{
lean_dec(v___x_2646_);
lean_dec_ref(v_f_2624_);
return v_init_2626_;
}
else
{
size_t v___x_2650_; size_t v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = lean_usize_of_nat(v___x_2646_);
lean_dec(v___x_2646_);
v___x_2651_ = lean_usize_of_nat(v___x_2647_);
v___x_2652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2624_, v_tail_2631_, v___x_2650_, v___x_2651_, v_init_2626_);
return v___x_2652_;
}
}
else
{
size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = lean_usize_of_nat(v___x_2646_);
lean_dec(v___x_2646_);
v___x_2654_ = lean_usize_of_nat(v___x_2647_);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2624_, v_tail_2631_, v___x_2653_, v___x_2654_, v_init_2626_);
return v___x_2655_;
}
}
}
}
else
{
lean_object* v_root_2656_; lean_object* v_tail_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v_root_2656_ = lean_ctor_get(v_t_2625_, 0);
v_tail_2657_ = lean_ctor_get(v_t_2625_, 1);
lean_inc_ref(v_f_2624_);
v___x_2658_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2624_, v_root_2656_, v_init_2626_);
v___x_2659_ = lean_array_get_size(v_tail_2657_);
v___x_2660_ = lean_nat_dec_lt(v___x_2628_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_dec_ref(v_f_2624_);
return v___x_2658_;
}
else
{
uint8_t v___x_2661_; 
v___x_2661_ = lean_nat_dec_le(v___x_2659_, v___x_2659_);
if (v___x_2661_ == 0)
{
if (v___x_2660_ == 0)
{
lean_dec_ref(v_f_2624_);
return v___x_2658_;
}
else
{
size_t v___x_2662_; size_t v___x_2663_; lean_object* v___x_2664_; 
v___x_2662_ = ((size_t)0ULL);
v___x_2663_ = lean_usize_of_nat(v___x_2659_);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2624_, v_tail_2657_, v___x_2662_, v___x_2663_, v___x_2658_);
return v___x_2664_;
}
}
else
{
size_t v___x_2665_; size_t v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = ((size_t)0ULL);
v___x_2666_ = lean_usize_of_nat(v___x_2659_);
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2624_, v_tail_2657_, v___x_2665_, v___x_2666_, v___x_2658_);
return v___x_2667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2668_, lean_object* v_t_2669_, lean_object* v_init_2670_, lean_object* v_start_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2668_, v_t_2669_, v_init_2670_, v_start_2671_);
lean_dec(v_start_2671_);
lean_dec_ref(v_t_2669_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2673_, lean_object* v_f_2674_){
_start:
{
lean_object* v_decls_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v_decls_2675_ = lean_ctor_get(v_lctx_2673_, 1);
lean_inc_ref(v_decls_2675_);
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2674_, v_decls_2675_, v_lctx_2673_, v___x_2676_);
lean_dec_ref(v_decls_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2678_, lean_object* v_fvarId_2679_, uint8_t v_kind_2680_){
_start:
{
lean_object* v_fvarIdToDecl_2681_; lean_object* v_decls_2682_; lean_object* v_auxDeclToFullName_2683_; lean_object* v___x_2684_; 
v_fvarIdToDecl_2681_ = lean_ctor_get(v_lctx_2678_, 0);
v_decls_2682_ = lean_ctor_get(v_lctx_2678_, 1);
v_auxDeclToFullName_2683_ = lean_ctor_get(v_lctx_2678_, 2);
lean_inc_ref(v_lctx_2678_);
v___x_2684_ = lean_local_ctx_find(v_lctx_2678_, v_fvarId_2679_);
if (lean_obj_tag(v___x_2684_) == 0)
{
return v_lctx_2678_;
}
else
{
lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2709_; 
lean_inc(v_auxDeclToFullName_2683_);
lean_inc_ref(v_decls_2682_);
lean_inc_ref(v_fvarIdToDecl_2681_);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_lctx_2678_);
if (v_isSharedCheck_2709_ == 0)
{
lean_object* v_unused_2710_; lean_object* v_unused_2711_; lean_object* v_unused_2712_; 
v_unused_2710_ = lean_ctor_get(v_lctx_2678_, 2);
lean_dec(v_unused_2710_);
v_unused_2711_ = lean_ctor_get(v_lctx_2678_, 1);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_lctx_2678_, 0);
lean_dec(v_unused_2712_);
v___x_2686_ = v_lctx_2678_;
v_isShared_2687_ = v_isSharedCheck_2709_;
goto v_resetjp_2685_;
}
else
{
lean_dec(v_lctx_2678_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2709_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_val_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2708_; 
v_val_2688_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2690_ = v___x_2684_;
v_isShared_2691_ = v_isSharedCheck_2708_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_val_2688_);
lean_dec(v___x_2684_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2708_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_decl_2692_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2704_; lean_object* v_fvarId_2707_; 
v_decl_2692_ = l_Lean_LocalDecl_setKind(v_val_2688_, v_kind_2680_);
v_fvarId_2707_ = lean_ctor_get(v_decl_2692_, 1);
lean_inc(v_fvarId_2707_);
v___y_2704_ = v_fvarId_2707_;
goto v___jp_2703_;
v___jp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v_decl_2692_);
v___x_2697_ = v___x_2690_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_decl_2692_);
v___x_2697_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2700_; 
v___x_2698_ = l_Lean_PersistentArray_set___redArg(v_decls_2682_, v___y_2695_, v___x_2697_);
lean_dec(v___y_2695_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 1, v___x_2698_);
lean_ctor_set(v___x_2686_, 0, v___y_2694_);
v___x_2700_ = v___x_2686_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___y_2694_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_auxDeclToFullName_2683_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
v___jp_2703_:
{
lean_object* v___x_2705_; lean_object* v_index_2706_; 
lean_inc_ref(v_decl_2692_);
v___x_2705_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2681_, v___y_2704_, v_decl_2692_);
v_index_2706_ = lean_ctor_get(v_decl_2692_, 0);
lean_inc(v_index_2706_);
v___y_2694_ = v___x_2705_;
v___y_2695_ = v_index_2706_;
goto v___jp_2693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2713_, lean_object* v_fvarId_2714_, lean_object* v_kind_2715_){
_start:
{
uint8_t v_kind_boxed_2716_; lean_object* v_res_2717_; 
v_kind_boxed_2716_ = lean_unbox(v_kind_2715_);
v_res_2717_ = l_Lean_LocalContext_setKind(v_lctx_2713_, v_fvarId_2714_, v_kind_boxed_2716_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2718_, lean_object* v_fvarId_2719_, uint8_t v_bi_2720_){
_start:
{
lean_object* v_fvarIdToDecl_2721_; lean_object* v_decls_2722_; lean_object* v_auxDeclToFullName_2723_; lean_object* v___x_2724_; 
v_fvarIdToDecl_2721_ = lean_ctor_get(v_lctx_2718_, 0);
v_decls_2722_ = lean_ctor_get(v_lctx_2718_, 1);
v_auxDeclToFullName_2723_ = lean_ctor_get(v_lctx_2718_, 2);
lean_inc_ref(v_lctx_2718_);
v___x_2724_ = lean_local_ctx_find(v_lctx_2718_, v_fvarId_2719_);
if (lean_obj_tag(v___x_2724_) == 0)
{
return v_lctx_2718_;
}
else
{
lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2749_; 
lean_inc(v_auxDeclToFullName_2723_);
lean_inc_ref(v_decls_2722_);
lean_inc_ref(v_fvarIdToDecl_2721_);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_lctx_2718_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; 
v_unused_2750_ = lean_ctor_get(v_lctx_2718_, 2);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_lctx_2718_, 1);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_lctx_2718_, 0);
lean_dec(v_unused_2752_);
v___x_2726_ = v_lctx_2718_;
v_isShared_2727_ = v_isSharedCheck_2749_;
goto v_resetjp_2725_;
}
else
{
lean_dec(v_lctx_2718_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2749_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v_val_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2748_; 
v_val_2728_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2730_ = v___x_2724_;
v_isShared_2731_ = v_isSharedCheck_2748_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_val_2728_);
lean_dec(v___x_2724_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2748_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v_decl_2732_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2744_; lean_object* v_fvarId_2747_; 
v_decl_2732_ = l_Lean_LocalDecl_setBinderInfo(v_val_2728_, v_bi_2720_);
v_fvarId_2747_ = lean_ctor_get(v_decl_2732_, 1);
lean_inc(v_fvarId_2747_);
v___y_2744_ = v_fvarId_2747_;
goto v___jp_2743_;
v___jp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v_decl_2732_);
v___x_2737_ = v___x_2730_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_decl_2732_);
v___x_2737_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2738_ = l_Lean_PersistentArray_set___redArg(v_decls_2722_, v___y_2735_, v___x_2737_);
lean_dec(v___y_2735_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 1, v___x_2738_);
lean_ctor_set(v___x_2726_, 0, v___y_2734_);
v___x_2740_ = v___x_2726_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___y_2734_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_auxDeclToFullName_2723_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
v___jp_2743_:
{
lean_object* v___x_2745_; lean_object* v_index_2746_; 
lean_inc_ref(v_decl_2732_);
v___x_2745_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2721_, v___y_2744_, v_decl_2732_);
v_index_2746_ = lean_ctor_get(v_decl_2732_, 0);
lean_inc(v_index_2746_);
v___y_2734_ = v___x_2745_;
v___y_2735_ = v_index_2746_;
goto v___jp_2733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2753_, lean_object* v_fvarId_2754_, lean_object* v_bi_2755_){
_start:
{
uint8_t v_bi_boxed_2756_; lean_object* v_res_2757_; 
v_bi_boxed_2756_ = lean_unbox(v_bi_2755_);
v_res_2757_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2753_, v_fvarId_2754_, v_bi_boxed_2756_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object* v_lctx_2758_, lean_object* v_fvarId_2759_, lean_object* v_type_2760_){
_start:
{
lean_object* v_fvarIdToDecl_2761_; lean_object* v_decls_2762_; lean_object* v_auxDeclToFullName_2763_; lean_object* v___x_2764_; 
v_fvarIdToDecl_2761_ = lean_ctor_get(v_lctx_2758_, 0);
v_decls_2762_ = lean_ctor_get(v_lctx_2758_, 1);
v_auxDeclToFullName_2763_ = lean_ctor_get(v_lctx_2758_, 2);
lean_inc_ref(v_lctx_2758_);
v___x_2764_ = lean_local_ctx_find(v_lctx_2758_, v_fvarId_2759_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_dec_ref(v_type_2760_);
return v_lctx_2758_;
}
else
{
lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2789_; 
lean_inc(v_auxDeclToFullName_2763_);
lean_inc_ref(v_decls_2762_);
lean_inc_ref(v_fvarIdToDecl_2761_);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_lctx_2758_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; lean_object* v_unused_2791_; lean_object* v_unused_2792_; 
v_unused_2790_ = lean_ctor_get(v_lctx_2758_, 2);
lean_dec(v_unused_2790_);
v_unused_2791_ = lean_ctor_get(v_lctx_2758_, 1);
lean_dec(v_unused_2791_);
v_unused_2792_ = lean_ctor_get(v_lctx_2758_, 0);
lean_dec(v_unused_2792_);
v___x_2766_ = v_lctx_2758_;
v_isShared_2767_ = v_isSharedCheck_2789_;
goto v_resetjp_2765_;
}
else
{
lean_dec(v_lctx_2758_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2789_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v_val_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2788_; 
v_val_2768_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2770_ = v___x_2764_;
v_isShared_2771_ = v_isSharedCheck_2788_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_val_2768_);
lean_dec(v___x_2764_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2788_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v_decl_2772_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2784_; lean_object* v_fvarId_2787_; 
v_decl_2772_ = l_Lean_LocalDecl_setType(v_val_2768_, v_type_2760_);
v_fvarId_2787_ = lean_ctor_get(v_decl_2772_, 1);
lean_inc(v_fvarId_2787_);
v___y_2784_ = v_fvarId_2787_;
goto v___jp_2783_;
v___jp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v_decl_2772_);
v___x_2777_ = v___x_2770_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_decl_2772_);
v___x_2777_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; lean_object* v___x_2780_; 
v___x_2778_ = l_Lean_PersistentArray_set___redArg(v_decls_2762_, v___y_2775_, v___x_2777_);
lean_dec(v___y_2775_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 1, v___x_2778_);
lean_ctor_set(v___x_2766_, 0, v___y_2774_);
v___x_2780_ = v___x_2766_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___y_2774_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2781_, 2, v_auxDeclToFullName_2763_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
v___jp_2783_:
{
lean_object* v___x_2785_; lean_object* v_index_2786_; 
lean_inc_ref(v_decl_2772_);
v___x_2785_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2761_, v___y_2784_, v_decl_2772_);
v_index_2786_ = lean_ctor_get(v_decl_2772_, 0);
lean_inc(v_index_2786_);
v___y_2774_ = v___x_2785_;
v___y_2775_ = v_index_2786_;
goto v___jp_2773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2793_){
_start:
{
lean_object* v_decls_2794_; lean_object* v_size_2795_; 
v_decls_2794_ = lean_ctor_get(v_lctx_2793_, 1);
lean_inc_ref(v_decls_2794_);
lean_dec_ref(v_lctx_2793_);
v_size_2795_ = lean_ctor_get(v_decls_2794_, 2);
lean_inc(v_size_2795_);
lean_dec_ref(v_decls_2794_);
return v_size_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2796_, lean_object* v_i_2797_){
_start:
{
lean_object* v_decls_2798_; lean_object* v_size_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v_decls_2798_ = lean_ctor_get(v_lctx_2796_, 1);
v_size_2799_ = lean_ctor_get(v_decls_2798_, 2);
v___x_2800_ = lean_box(0);
v___x_2801_ = lean_nat_dec_lt(v_i_2797_, v_size_2799_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; 
v___x_2802_ = l_outOfBounds___redArg(v___x_2800_);
return v___x_2802_;
}
else
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2800_, v_decls_2798_, v_i_2797_);
return v___x_2803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2804_, lean_object* v_i_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2804_, v_i_2805_);
lean_dec(v_i_2805_);
lean_dec_ref(v_lctx_2804_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2807_, lean_object* v_f_2808_, lean_object* v_b_2809_, lean_object* v_decl_2810_){
_start:
{
if (lean_obj_tag(v_decl_2810_) == 0)
{
lean_object* v___x_2811_; 
lean_dec(v_f_2808_);
v___x_2811_ = lean_apply_2(v_toPure_2807_, lean_box(0), v_b_2809_);
return v___x_2811_;
}
else
{
lean_object* v_val_2812_; lean_object* v___x_2813_; 
lean_dec(v_toPure_2807_);
v_val_2812_ = lean_ctor_get(v_decl_2810_, 0);
lean_inc(v_val_2812_);
lean_dec_ref_known(v_decl_2810_, 1);
v___x_2813_ = lean_apply_2(v_f_2808_, v_b_2809_, v_val_2812_);
return v___x_2813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2814_, lean_object* v_lctx_2815_, lean_object* v_f_2816_, lean_object* v_init_2817_, lean_object* v_start_2818_){
_start:
{
lean_object* v_toApplicative_2819_; lean_object* v_decls_2820_; lean_object* v_toPure_2821_; lean_object* v___f_2822_; lean_object* v___x_2823_; 
v_toApplicative_2819_ = lean_ctor_get(v_inst_2814_, 0);
v_decls_2820_ = lean_ctor_get(v_lctx_2815_, 1);
lean_inc_ref(v_decls_2820_);
lean_dec_ref(v_lctx_2815_);
v_toPure_2821_ = lean_ctor_get(v_toApplicative_2819_, 1);
lean_inc(v_toPure_2821_);
v___f_2822_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2822_, 0, v_toPure_2821_);
lean_closure_set(v___f_2822_, 1, v_f_2816_);
v___x_2823_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2814_, v_decls_2820_, v___f_2822_, v_init_2817_, v_start_2818_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2824_, lean_object* v_lctx_2825_, lean_object* v_f_2826_, lean_object* v_init_2827_, lean_object* v_start_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2824_, v_lctx_2825_, v_f_2826_, v_init_2827_, v_start_2828_);
lean_dec(v_start_2828_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2830_, lean_object* v_00_u03b2_2831_, lean_object* v_inst_2832_, lean_object* v_lctx_2833_, lean_object* v_f_2834_, lean_object* v_init_2835_, lean_object* v_start_2836_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2832_, v_lctx_2833_, v_f_2834_, v_init_2835_, v_start_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2838_, lean_object* v_00_u03b2_2839_, lean_object* v_inst_2840_, lean_object* v_lctx_2841_, lean_object* v_f_2842_, lean_object* v_init_2843_, lean_object* v_start_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_LocalContext_foldlM(v_m_2838_, v_00_u03b2_2839_, v_inst_2840_, v_lctx_2841_, v_f_2842_, v_init_2843_, v_start_2844_);
lean_dec(v_start_2844_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2846_, lean_object* v_f_2847_, lean_object* v_decl_2848_, lean_object* v_b_2849_){
_start:
{
if (lean_obj_tag(v_decl_2848_) == 0)
{
lean_object* v___x_2850_; 
lean_dec(v_f_2847_);
v___x_2850_ = lean_apply_2(v_toPure_2846_, lean_box(0), v_b_2849_);
return v___x_2850_;
}
else
{
lean_object* v_val_2851_; lean_object* v___x_2852_; 
lean_dec(v_toPure_2846_);
v_val_2851_ = lean_ctor_get(v_decl_2848_, 0);
lean_inc(v_val_2851_);
lean_dec_ref_known(v_decl_2848_, 1);
v___x_2852_ = lean_apply_2(v_f_2847_, v_val_2851_, v_b_2849_);
return v___x_2852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2853_, lean_object* v_lctx_2854_, lean_object* v_f_2855_, lean_object* v_init_2856_){
_start:
{
lean_object* v_toApplicative_2857_; lean_object* v_decls_2858_; lean_object* v_toPure_2859_; lean_object* v___f_2860_; lean_object* v___x_2861_; 
v_toApplicative_2857_ = lean_ctor_get(v_inst_2853_, 0);
v_decls_2858_ = lean_ctor_get(v_lctx_2854_, 1);
lean_inc_ref(v_decls_2858_);
lean_dec_ref(v_lctx_2854_);
v_toPure_2859_ = lean_ctor_get(v_toApplicative_2857_, 1);
lean_inc(v_toPure_2859_);
v___f_2860_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2860_, 0, v_toPure_2859_);
lean_closure_set(v___f_2860_, 1, v_f_2855_);
v___x_2861_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2853_, v_decls_2858_, v___f_2860_, v_init_2856_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2862_, lean_object* v_00_u03b2_2863_, lean_object* v_inst_2864_, lean_object* v_lctx_2865_, lean_object* v_f_2866_, lean_object* v_init_2867_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2864_, v_lctx_2865_, v_f_2866_, v_init_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2869_, lean_object* v_f_2870_, lean_object* v_decl_2871_){
_start:
{
if (lean_obj_tag(v_decl_2871_) == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec(v_f_2870_);
v___x_2872_ = lean_box(0);
v___x_2873_ = lean_apply_2(v_toPure_2869_, lean_box(0), v___x_2872_);
return v___x_2873_;
}
else
{
lean_object* v_val_2874_; lean_object* v___x_2875_; 
lean_dec(v_toPure_2869_);
v_val_2874_ = lean_ctor_get(v_decl_2871_, 0);
lean_inc(v_val_2874_);
lean_dec_ref_known(v_decl_2871_, 1);
v___x_2875_ = lean_apply_1(v_f_2870_, v_val_2874_);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2876_, lean_object* v_lctx_2877_, lean_object* v_f_2878_, lean_object* v_start_2879_){
_start:
{
lean_object* v_toApplicative_2880_; lean_object* v_decls_2881_; lean_object* v_toPure_2882_; lean_object* v___f_2883_; lean_object* v___x_2884_; 
v_toApplicative_2880_ = lean_ctor_get(v_inst_2876_, 0);
v_decls_2881_ = lean_ctor_get(v_lctx_2877_, 1);
lean_inc_ref(v_decls_2881_);
lean_dec_ref(v_lctx_2877_);
v_toPure_2882_ = lean_ctor_get(v_toApplicative_2880_, 1);
lean_inc(v_toPure_2882_);
v___f_2883_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2883_, 0, v_toPure_2882_);
lean_closure_set(v___f_2883_, 1, v_f_2878_);
v___x_2884_ = l_Lean_PersistentArray_forM___redArg(v_inst_2876_, v_decls_2881_, v___f_2883_, v_start_2879_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2885_, lean_object* v_lctx_2886_, lean_object* v_f_2887_, lean_object* v_start_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_LocalContext_forM___redArg(v_inst_2885_, v_lctx_2886_, v_f_2887_, v_start_2888_);
lean_dec(v_start_2888_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2890_, lean_object* v_inst_2891_, lean_object* v_lctx_2892_, lean_object* v_f_2893_, lean_object* v_start_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_LocalContext_forM___redArg(v_inst_2891_, v_lctx_2892_, v_f_2893_, v_start_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2896_, lean_object* v_inst_2897_, lean_object* v_lctx_2898_, lean_object* v_f_2899_, lean_object* v_start_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_LocalContext_forM(v_m_2896_, v_inst_2897_, v_lctx_2898_, v_f_2899_, v_start_2900_);
lean_dec(v_start_2900_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2902_, lean_object* v_f_2903_, lean_object* v_decl_2904_){
_start:
{
if (lean_obj_tag(v_decl_2904_) == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
lean_dec(v_f_2903_);
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_apply_2(v_toPure_2902_, lean_box(0), v___x_2905_);
return v___x_2906_;
}
else
{
lean_object* v_val_2907_; lean_object* v___x_2908_; 
lean_dec(v_toPure_2902_);
v_val_2907_ = lean_ctor_get(v_decl_2904_, 0);
lean_inc(v_val_2907_);
lean_dec_ref_known(v_decl_2904_, 1);
v___x_2908_ = lean_apply_1(v_f_2903_, v_val_2907_);
return v___x_2908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2909_, lean_object* v_lctx_2910_, lean_object* v_f_2911_){
_start:
{
lean_object* v_toApplicative_2912_; lean_object* v_decls_2913_; lean_object* v_toPure_2914_; lean_object* v___f_2915_; lean_object* v___x_2916_; 
v_toApplicative_2912_ = lean_ctor_get(v_inst_2909_, 0);
v_decls_2913_ = lean_ctor_get(v_lctx_2910_, 1);
lean_inc_ref(v_decls_2913_);
lean_dec_ref(v_lctx_2910_);
v_toPure_2914_ = lean_ctor_get(v_toApplicative_2912_, 1);
lean_inc(v_toPure_2914_);
v___f_2915_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2915_, 0, v_toPure_2914_);
lean_closure_set(v___f_2915_, 1, v_f_2911_);
v___x_2916_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2909_, v_decls_2913_, v___f_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2917_, lean_object* v_00_u03b2_2918_, lean_object* v_inst_2919_, lean_object* v_lctx_2920_, lean_object* v_f_2921_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2919_, v_lctx_2920_, v_f_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2923_, lean_object* v_lctx_2924_, lean_object* v_f_2925_){
_start:
{
lean_object* v_toApplicative_2926_; lean_object* v_decls_2927_; lean_object* v_toPure_2928_; lean_object* v___f_2929_; lean_object* v___x_2930_; 
v_toApplicative_2926_ = lean_ctor_get(v_inst_2923_, 0);
v_decls_2927_ = lean_ctor_get(v_lctx_2924_, 1);
lean_inc_ref(v_decls_2927_);
lean_dec_ref(v_lctx_2924_);
v_toPure_2928_ = lean_ctor_get(v_toApplicative_2926_, 1);
lean_inc(v_toPure_2928_);
v___f_2929_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2929_, 0, v_toPure_2928_);
lean_closure_set(v___f_2929_, 1, v_f_2925_);
v___x_2930_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2923_, v_decls_2927_, v___f_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2931_, lean_object* v_00_u03b2_2932_, lean_object* v_inst_2933_, lean_object* v_lctx_2934_, lean_object* v_f_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2933_, v_lctx_2934_, v_f_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2937_, lean_object* v_f_2938_, lean_object* v_d_x3f_2939_, lean_object* v_b_2940_){
_start:
{
if (lean_obj_tag(v_d_x3f_2939_) == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec(v_f_2938_);
v___x_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_b_2940_);
v___x_2942_ = lean_apply_2(v_toPure_2937_, lean_box(0), v___x_2941_);
return v___x_2942_;
}
else
{
lean_object* v_val_2943_; lean_object* v___x_2944_; 
lean_dec(v_toPure_2937_);
v_val_2943_ = lean_ctor_get(v_d_x3f_2939_, 0);
lean_inc(v_val_2943_);
lean_dec_ref_known(v_d_x3f_2939_, 1);
v___x_2944_ = lean_apply_2(v_f_2938_, v_val_2943_, v_b_2940_);
return v___x_2944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2945_, lean_object* v_inst_2946_, lean_object* v_00_u03b2_2947_, lean_object* v_lctx_2948_, lean_object* v_init_2949_, lean_object* v_f_2950_){
_start:
{
lean_object* v_decls_2951_; lean_object* v___f_2952_; lean_object* v___x_2953_; 
v_decls_2951_ = lean_ctor_get(v_lctx_2948_, 1);
v___f_2952_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2952_, 0, v_toPure_2945_);
lean_closure_set(v___f_2952_, 1, v_f_2950_);
v___x_2953_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2946_, v_decls_2951_, v_init_2949_, v___f_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object* v_toPure_2954_, lean_object* v_inst_2955_, lean_object* v_00_u03b2_2956_, lean_object* v_lctx_2957_, lean_object* v_init_2958_, lean_object* v_f_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(v_toPure_2954_, v_inst_2955_, v_00_u03b2_2956_, v_lctx_2957_, v_init_2958_, v_f_2959_);
lean_dec_ref(v_lctx_2957_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2961_){
_start:
{
lean_object* v_toApplicative_2962_; lean_object* v_toPure_2963_; lean_object* v___f_2964_; 
v_toApplicative_2962_ = lean_ctor_get(v_inst_2961_, 0);
v_toPure_2963_ = lean_ctor_get(v_toApplicative_2962_, 1);
lean_inc(v_toPure_2963_);
v___f_2964_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2964_, 0, v_toPure_2963_);
lean_closure_set(v___f_2964_, 1, v_inst_2961_);
return v___f_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2965_, lean_object* v_inst_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2968_, lean_object* v_x1_2969_, lean_object* v_x2_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_apply_2(v_f_2968_, v_x1_2969_, v_x2_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2991_, lean_object* v_f_2992_, lean_object* v_init_2993_, lean_object* v_start_2994_){
_start:
{
lean_object* v___f_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___f_2995_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2995_, 0, v_f_2992_);
v___x_2996_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2997_ = l_Lean_LocalContext_foldlM___redArg(v___x_2996_, v_lctx_2991_, v___f_2995_, v_init_2993_, v_start_2994_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_2998_, lean_object* v_f_2999_, lean_object* v_init_3000_, lean_object* v_start_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_LocalContext_foldl___redArg(v_lctx_2998_, v_f_2999_, v_init_3000_, v_start_3001_);
lean_dec(v_start_3001_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_3003_, lean_object* v_lctx_3004_, lean_object* v_f_3005_, lean_object* v_init_3006_, lean_object* v_start_3007_){
_start:
{
lean_object* v___f_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___f_3008_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3008_, 0, v_f_3005_);
v___x_3009_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3010_ = l_Lean_LocalContext_foldlM___redArg(v___x_3009_, v_lctx_3004_, v___f_3008_, v_init_3006_, v_start_3007_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_3011_, lean_object* v_lctx_3012_, lean_object* v_f_3013_, lean_object* v_init_3014_, lean_object* v_start_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_LocalContext_foldl(v_00_u03b2_3011_, v_lctx_3012_, v_f_3013_, v_init_3014_, v_start_3015_);
lean_dec(v_start_3015_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_3017_, lean_object* v_x1_3018_, lean_object* v_x2_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_apply_2(v_f_3017_, v_x1_3018_, v_x2_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_3021_, lean_object* v_f_3022_, lean_object* v_init_3023_){
_start:
{
lean_object* v___f_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___f_3024_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_3024_, 0, v_f_3022_);
v___x_3025_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3026_ = l_Lean_LocalContext_foldrM___redArg(v___x_3025_, v_lctx_3021_, v___f_3024_, v_init_3023_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_3027_, lean_object* v_lctx_3028_, lean_object* v_f_3029_, lean_object* v_init_3030_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_3034_, size_t v_i_3035_, size_t v_stop_3036_, lean_object* v_b_3037_){
_start:
{
lean_object* v___y_3039_; uint8_t v___x_3043_; 
v___x_3043_ = lean_usize_dec_eq(v_i_3035_, v_stop_3036_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_array_uget_borrowed(v_as_3034_, v_i_3035_);
if (lean_obj_tag(v___x_3044_) == 0)
{
v___y_3039_ = v_b_3037_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = lean_unsigned_to_nat(1u);
v___x_3046_ = lean_nat_add(v_b_3037_, v___x_3045_);
lean_dec(v_b_3037_);
v___y_3039_ = v___x_3046_;
goto v___jp_3038_;
}
}
else
{
return v_b_3037_;
}
v___jp_3038_:
{
size_t v___x_3040_; size_t v___x_3041_; 
v___x_3040_ = ((size_t)1ULL);
v___x_3041_ = lean_usize_add(v_i_3035_, v___x_3040_);
v_i_3035_ = v___x_3041_;
v_b_3037_ = v___y_3039_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3047_, lean_object* v_i_3048_, lean_object* v_stop_3049_, lean_object* v_b_3050_){
_start:
{
size_t v_i_boxed_3051_; size_t v_stop_boxed_3052_; lean_object* v_res_3053_; 
v_i_boxed_3051_ = lean_unbox_usize(v_i_3048_);
lean_dec(v_i_3048_);
v_stop_boxed_3052_ = lean_unbox_usize(v_stop_3049_);
lean_dec(v_stop_3049_);
v_res_3053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_3047_, v_i_boxed_3051_, v_stop_boxed_3052_, v_b_3050_);
lean_dec_ref(v_as_3047_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_3054_, lean_object* v_x_3055_){
_start:
{
if (lean_obj_tag(v_x_3054_) == 0)
{
lean_object* v_cs_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; 
v_cs_3056_ = lean_ctor_get(v_x_3054_, 0);
v___x_3057_ = lean_unsigned_to_nat(0u);
v___x_3058_ = lean_array_get_size(v_cs_3056_);
v___x_3059_ = lean_nat_dec_lt(v___x_3057_, v___x_3058_);
if (v___x_3059_ == 0)
{
return v_x_3055_;
}
else
{
uint8_t v___x_3060_; 
v___x_3060_ = lean_nat_dec_le(v___x_3058_, v___x_3058_);
if (v___x_3060_ == 0)
{
if (v___x_3059_ == 0)
{
return v_x_3055_;
}
else
{
size_t v___x_3061_; size_t v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = ((size_t)0ULL);
v___x_3062_ = lean_usize_of_nat(v___x_3058_);
v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3056_, v___x_3061_, v___x_3062_, v_x_3055_);
return v___x_3063_;
}
}
else
{
size_t v___x_3064_; size_t v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = ((size_t)0ULL);
v___x_3065_ = lean_usize_of_nat(v___x_3058_);
v___x_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3056_, v___x_3064_, v___x_3065_, v_x_3055_);
return v___x_3066_;
}
}
}
else
{
lean_object* v_vs_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v_vs_3067_ = lean_ctor_get(v_x_3054_, 0);
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3069_ = lean_array_get_size(v_vs_3067_);
v___x_3070_ = lean_nat_dec_lt(v___x_3068_, v___x_3069_);
if (v___x_3070_ == 0)
{
return v_x_3055_;
}
else
{
uint8_t v___x_3071_; 
v___x_3071_ = lean_nat_dec_le(v___x_3069_, v___x_3069_);
if (v___x_3071_ == 0)
{
if (v___x_3070_ == 0)
{
return v_x_3055_;
}
else
{
size_t v___x_3072_; size_t v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = ((size_t)0ULL);
v___x_3073_ = lean_usize_of_nat(v___x_3069_);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3067_, v___x_3072_, v___x_3073_, v_x_3055_);
return v___x_3074_;
}
}
else
{
size_t v___x_3075_; size_t v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = ((size_t)0ULL);
v___x_3076_ = lean_usize_of_nat(v___x_3069_);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3067_, v___x_3075_, v___x_3076_, v_x_3055_);
return v___x_3077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3078_, size_t v_i_3079_, size_t v_stop_3080_, lean_object* v_b_3081_){
_start:
{
uint8_t v___x_3082_; 
v___x_3082_ = lean_usize_dec_eq(v_i_3079_, v_stop_3080_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; size_t v___x_3085_; size_t v___x_3086_; 
v___x_3083_ = lean_array_uget_borrowed(v_as_3078_, v_i_3079_);
v___x_3084_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3083_, v_b_3081_);
v___x_3085_ = ((size_t)1ULL);
v___x_3086_ = lean_usize_add(v_i_3079_, v___x_3085_);
v_i_3079_ = v___x_3086_;
v_b_3081_ = v___x_3084_;
goto _start;
}
else
{
return v_b_3081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3088_, lean_object* v_i_3089_, lean_object* v_stop_3090_, lean_object* v_b_3091_){
_start:
{
size_t v_i_boxed_3092_; size_t v_stop_boxed_3093_; lean_object* v_res_3094_; 
v_i_boxed_3092_ = lean_unbox_usize(v_i_3089_);
lean_dec(v_i_3089_);
v_stop_boxed_3093_ = lean_unbox_usize(v_stop_3090_);
lean_dec(v_stop_3090_);
v_res_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3088_, v_i_boxed_3092_, v_stop_boxed_3093_, v_b_3091_);
lean_dec_ref(v_as_3088_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3095_, lean_object* v_x_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3095_, v_x_3096_);
lean_dec_ref(v_x_3095_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3098_, size_t v_x_3099_, size_t v_x_3100_, lean_object* v_x_3101_){
_start:
{
if (lean_obj_tag(v_x_3098_) == 0)
{
lean_object* v_cs_3102_; lean_object* v___x_3103_; size_t v___x_3104_; lean_object* v_j_3105_; lean_object* v___x_3106_; size_t v___x_3107_; size_t v___x_3108_; size_t v___x_3109_; size_t v___x_3110_; size_t v___x_3111_; size_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; uint8_t v___x_3117_; 
v_cs_3102_ = lean_ctor_get(v_x_3098_, 0);
v___x_3103_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3104_ = lean_usize_shift_right(v_x_3099_, v_x_3100_);
v_j_3105_ = lean_usize_to_nat(v___x_3104_);
v___x_3106_ = lean_array_get_borrowed(v___x_3103_, v_cs_3102_, v_j_3105_);
v___x_3107_ = ((size_t)1ULL);
v___x_3108_ = lean_usize_shift_left(v___x_3107_, v_x_3100_);
v___x_3109_ = lean_usize_sub(v___x_3108_, v___x_3107_);
v___x_3110_ = lean_usize_land(v_x_3099_, v___x_3109_);
v___x_3111_ = ((size_t)5ULL);
v___x_3112_ = lean_usize_sub(v_x_3100_, v___x_3111_);
v___x_3113_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3106_, v___x_3110_, v___x_3112_, v_x_3101_);
v___x_3114_ = lean_unsigned_to_nat(1u);
v___x_3115_ = lean_nat_add(v_j_3105_, v___x_3114_);
lean_dec(v_j_3105_);
v___x_3116_ = lean_array_get_size(v_cs_3102_);
v___x_3117_ = lean_nat_dec_lt(v___x_3115_, v___x_3116_);
if (v___x_3117_ == 0)
{
lean_dec(v___x_3115_);
return v___x_3113_;
}
else
{
uint8_t v___x_3118_; 
v___x_3118_ = lean_nat_dec_le(v___x_3116_, v___x_3116_);
if (v___x_3118_ == 0)
{
if (v___x_3117_ == 0)
{
lean_dec(v___x_3115_);
return v___x_3113_;
}
else
{
size_t v___x_3119_; size_t v___x_3120_; lean_object* v___x_3121_; 
v___x_3119_ = lean_usize_of_nat(v___x_3115_);
lean_dec(v___x_3115_);
v___x_3120_ = lean_usize_of_nat(v___x_3116_);
v___x_3121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3102_, v___x_3119_, v___x_3120_, v___x_3113_);
return v___x_3121_;
}
}
else
{
size_t v___x_3122_; size_t v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = lean_usize_of_nat(v___x_3115_);
lean_dec(v___x_3115_);
v___x_3123_ = lean_usize_of_nat(v___x_3116_);
v___x_3124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3102_, v___x_3122_, v___x_3123_, v___x_3113_);
return v___x_3124_;
}
}
}
else
{
lean_object* v_vs_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v_vs_3125_ = lean_ctor_get(v_x_3098_, 0);
v___x_3126_ = lean_usize_to_nat(v_x_3099_);
v___x_3127_ = lean_array_get_size(v_vs_3125_);
v___x_3128_ = lean_nat_dec_lt(v___x_3126_, v___x_3127_);
if (v___x_3128_ == 0)
{
lean_dec(v___x_3126_);
return v_x_3101_;
}
else
{
uint8_t v___x_3129_; 
v___x_3129_ = lean_nat_dec_le(v___x_3127_, v___x_3127_);
if (v___x_3129_ == 0)
{
if (v___x_3128_ == 0)
{
lean_dec(v___x_3126_);
return v_x_3101_;
}
else
{
size_t v___x_3130_; size_t v___x_3131_; lean_object* v___x_3132_; 
v___x_3130_ = lean_usize_of_nat(v___x_3126_);
lean_dec(v___x_3126_);
v___x_3131_ = lean_usize_of_nat(v___x_3127_);
v___x_3132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3125_, v___x_3130_, v___x_3131_, v_x_3101_);
return v___x_3132_;
}
}
else
{
size_t v___x_3133_; size_t v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = lean_usize_of_nat(v___x_3126_);
lean_dec(v___x_3126_);
v___x_3134_ = lean_usize_of_nat(v___x_3127_);
v___x_3135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3125_, v___x_3133_, v___x_3134_, v_x_3101_);
return v___x_3135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3136_, lean_object* v_x_3137_, lean_object* v_x_3138_, lean_object* v_x_3139_){
_start:
{
size_t v_x_1557__boxed_3140_; size_t v_x_1558__boxed_3141_; lean_object* v_res_3142_; 
v_x_1557__boxed_3140_ = lean_unbox_usize(v_x_3137_);
lean_dec(v_x_3137_);
v_x_1558__boxed_3141_ = lean_unbox_usize(v_x_3138_);
lean_dec(v_x_3138_);
v_res_3142_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3136_, v_x_1557__boxed_3140_, v_x_1558__boxed_3141_, v_x_3139_);
lean_dec_ref(v_x_3136_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3143_, lean_object* v_init_3144_, lean_object* v_start_3145_){
_start:
{
lean_object* v___x_3146_; uint8_t v___x_3147_; 
v___x_3146_ = lean_unsigned_to_nat(0u);
v___x_3147_ = lean_nat_dec_eq(v_start_3145_, v___x_3146_);
if (v___x_3147_ == 0)
{
lean_object* v_root_3148_; lean_object* v_tail_3149_; size_t v_shift_3150_; lean_object* v_tailOff_3151_; uint8_t v___x_3152_; 
v_root_3148_ = lean_ctor_get(v_t_3143_, 0);
v_tail_3149_ = lean_ctor_get(v_t_3143_, 1);
v_shift_3150_ = lean_ctor_get_usize(v_t_3143_, 4);
v_tailOff_3151_ = lean_ctor_get(v_t_3143_, 3);
v___x_3152_ = lean_nat_dec_le(v_tailOff_3151_, v_start_3145_);
if (v___x_3152_ == 0)
{
size_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; 
v___x_3153_ = lean_usize_of_nat(v_start_3145_);
v___x_3154_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3148_, v___x_3153_, v_shift_3150_, v_init_3144_);
v___x_3155_ = lean_array_get_size(v_tail_3149_);
v___x_3156_ = lean_nat_dec_lt(v___x_3146_, v___x_3155_);
if (v___x_3156_ == 0)
{
return v___x_3154_;
}
else
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_nat_dec_le(v___x_3155_, v___x_3155_);
if (v___x_3157_ == 0)
{
if (v___x_3156_ == 0)
{
return v___x_3154_;
}
else
{
size_t v___x_3158_; size_t v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = ((size_t)0ULL);
v___x_3159_ = lean_usize_of_nat(v___x_3155_);
v___x_3160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3149_, v___x_3158_, v___x_3159_, v___x_3154_);
return v___x_3160_;
}
}
else
{
size_t v___x_3161_; size_t v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = ((size_t)0ULL);
v___x_3162_ = lean_usize_of_nat(v___x_3155_);
v___x_3163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3149_, v___x_3161_, v___x_3162_, v___x_3154_);
return v___x_3163_;
}
}
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; uint8_t v___x_3166_; 
v___x_3164_ = lean_nat_sub(v_start_3145_, v_tailOff_3151_);
v___x_3165_ = lean_array_get_size(v_tail_3149_);
v___x_3166_ = lean_nat_dec_lt(v___x_3164_, v___x_3165_);
if (v___x_3166_ == 0)
{
lean_dec(v___x_3164_);
return v_init_3144_;
}
else
{
uint8_t v___x_3167_; 
v___x_3167_ = lean_nat_dec_le(v___x_3165_, v___x_3165_);
if (v___x_3167_ == 0)
{
if (v___x_3166_ == 0)
{
lean_dec(v___x_3164_);
return v_init_3144_;
}
else
{
size_t v___x_3168_; size_t v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = lean_usize_of_nat(v___x_3164_);
lean_dec(v___x_3164_);
v___x_3169_ = lean_usize_of_nat(v___x_3165_);
v___x_3170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3149_, v___x_3168_, v___x_3169_, v_init_3144_);
return v___x_3170_;
}
}
else
{
size_t v___x_3171_; size_t v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_usize_of_nat(v___x_3164_);
lean_dec(v___x_3164_);
v___x_3172_ = lean_usize_of_nat(v___x_3165_);
v___x_3173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3149_, v___x_3171_, v___x_3172_, v_init_3144_);
return v___x_3173_;
}
}
}
}
else
{
lean_object* v_root_3174_; lean_object* v_tail_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v_root_3174_ = lean_ctor_get(v_t_3143_, 0);
v_tail_3175_ = lean_ctor_get(v_t_3143_, 1);
v___x_3176_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3174_, v_init_3144_);
v___x_3177_ = lean_array_get_size(v_tail_3175_);
v___x_3178_ = lean_nat_dec_lt(v___x_3146_, v___x_3177_);
if (v___x_3178_ == 0)
{
return v___x_3176_;
}
else
{
uint8_t v___x_3179_; 
v___x_3179_ = lean_nat_dec_le(v___x_3177_, v___x_3177_);
if (v___x_3179_ == 0)
{
if (v___x_3178_ == 0)
{
return v___x_3176_;
}
else
{
size_t v___x_3180_; size_t v___x_3181_; lean_object* v___x_3182_; 
v___x_3180_ = ((size_t)0ULL);
v___x_3181_ = lean_usize_of_nat(v___x_3177_);
v___x_3182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3175_, v___x_3180_, v___x_3181_, v___x_3176_);
return v___x_3182_;
}
}
else
{
size_t v___x_3183_; size_t v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = ((size_t)0ULL);
v___x_3184_ = lean_usize_of_nat(v___x_3177_);
v___x_3185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3175_, v___x_3183_, v___x_3184_, v___x_3176_);
return v___x_3185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3186_, lean_object* v_init_3187_, lean_object* v_start_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3186_, v_init_3187_, v_start_3188_);
lean_dec(v_start_3188_);
lean_dec_ref(v_t_3186_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3190_, lean_object* v_init_3191_, lean_object* v_start_3192_){
_start:
{
lean_object* v_decls_3193_; lean_object* v___x_3194_; 
v_decls_3193_ = lean_ctor_get(v_lctx_3190_, 1);
v___x_3194_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3193_, v_init_3191_, v_start_3192_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3195_, lean_object* v_init_3196_, lean_object* v_start_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3195_, v_init_3196_, v_start_3197_);
lean_dec(v_start_3197_);
lean_dec_ref(v_lctx_3195_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3199_){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_unsigned_to_nat(0u);
v___x_3201_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3199_, v___x_3200_, v___x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Lean_LocalContext_size(v_lctx_3202_);
lean_dec_ref(v_lctx_3202_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3204_, lean_object* v_x_3205_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_apply_1(v_f_3204_, v_x_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3207_, lean_object* v_f_3208_){
_start:
{
lean_object* v___f_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___f_3209_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3209_, 0, v_f_3208_);
v___x_3210_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3211_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3210_, v_lctx_3207_, v___f_3209_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3212_, lean_object* v_lctx_3213_, lean_object* v_f_3214_){
_start:
{
lean_object* v___f_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___f_3215_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3215_, 0, v_f_3214_);
v___x_3216_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3217_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3216_, v_lctx_3213_, v___f_3215_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3218_, lean_object* v_f_3219_){
_start:
{
lean_object* v___f_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___f_3220_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3220_, 0, v_f_3219_);
v___x_3221_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3222_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3221_, v_lctx_3218_, v___f_3220_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3223_, lean_object* v_lctx_3224_, lean_object* v_f_3225_){
_start:
{
lean_object* v___f_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___f_3226_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3226_, 0, v_f_3225_);
v___x_3227_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3228_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3227_, v_lctx_3224_, v___f_3226_);
return v___x_3228_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3229_, lean_object* v_as_3230_, size_t v_i_3231_, size_t v_stop_3232_){
_start:
{
uint8_t v___x_3233_; 
v___x_3233_ = lean_usize_dec_eq(v_i_3231_, v_stop_3232_);
if (v___x_3233_ == 0)
{
uint8_t v___x_3234_; uint8_t v___y_3236_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v_fvarId_3242_; uint8_t v___x_3243_; 
v___x_3234_ = 1;
v___x_3240_ = lean_array_uget_borrowed(v_as_3230_, v_i_3231_);
v___x_3241_ = l_Lean_Expr_fvarId_x21(v___x_3240_);
v_fvarId_3242_ = lean_ctor_get(v_val_3229_, 1);
v___x_3243_ = l_Lean_instBEqFVarId_beq(v___x_3241_, v_fvarId_3242_);
lean_dec(v___x_3241_);
v___y_3236_ = v___x_3243_;
goto v___jp_3235_;
v___jp_3235_:
{
if (v___y_3236_ == 0)
{
size_t v___x_3237_; size_t v___x_3238_; 
v___x_3237_ = ((size_t)1ULL);
v___x_3238_ = lean_usize_add(v_i_3231_, v___x_3237_);
v_i_3231_ = v___x_3238_;
goto _start;
}
else
{
return v___x_3234_;
}
}
}
else
{
uint8_t v___x_3244_; 
v___x_3244_ = 0;
return v___x_3244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3245_, lean_object* v_as_3246_, lean_object* v_i_3247_, lean_object* v_stop_3248_){
_start:
{
size_t v_i_boxed_3249_; size_t v_stop_boxed_3250_; uint8_t v_res_3251_; lean_object* v_r_3252_; 
v_i_boxed_3249_ = lean_unbox_usize(v_i_3247_);
lean_dec(v_i_3247_);
v_stop_boxed_3250_ = lean_unbox_usize(v_stop_3248_);
lean_dec(v_stop_3248_);
v_res_3251_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3245_, v_as_3246_, v_i_boxed_3249_, v_stop_boxed_3250_);
lean_dec_ref(v_as_3246_);
lean_dec_ref(v_val_3245_);
v_r_3252_ = lean_box(v_res_3251_);
return v_r_3252_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3253_, lean_object* v_a_u2082_3254_, lean_object* v_exceptFVars_3255_, lean_object* v_i_3256_, lean_object* v_j_3257_){
_start:
{
lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v_size_3273_; uint8_t v___x_3274_; 
v_size_3273_ = lean_ctor_get(v_a_u2081_3253_, 2);
v___x_3274_ = lean_nat_dec_lt(v_i_3256_, v_size_3273_);
if (v___x_3274_ == 0)
{
uint8_t v___x_3275_; 
lean_dec(v_j_3257_);
lean_dec(v_i_3256_);
v___x_3275_ = 1;
return v___x_3275_;
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = lean_box(0);
v___x_3277_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3276_, v_a_u2081_3253_, v_i_3256_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = lean_unsigned_to_nat(1u);
v___x_3279_ = lean_nat_add(v_i_3256_, v___x_3278_);
lean_dec(v_i_3256_);
v_i_3256_ = v___x_3279_;
goto _start;
}
else
{
lean_object* v_val_3281_; uint8_t v___y_3283_; lean_object* v___x_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; 
v_val_3281_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_val_3281_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3292_ = lean_unsigned_to_nat(0u);
v___x_3293_ = lean_array_get_size(v_exceptFVars_3255_);
v___x_3294_ = lean_nat_dec_lt(v___x_3292_, v___x_3293_);
if (v___x_3294_ == 0)
{
v___y_3283_ = v___x_3294_;
goto v___jp_3282_;
}
else
{
if (v___x_3294_ == 0)
{
v___y_3283_ = v___x_3294_;
goto v___jp_3282_;
}
else
{
size_t v___x_3295_; size_t v___x_3296_; uint8_t v___x_3297_; 
v___x_3295_ = ((size_t)0ULL);
v___x_3296_ = lean_usize_of_nat(v___x_3293_);
v___x_3297_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3281_, v_exceptFVars_3255_, v___x_3295_, v___x_3296_);
if (v___x_3297_ == 0)
{
v___y_3283_ = v___x_3297_;
goto v___jp_3282_;
}
else
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec(v_val_3281_);
v___x_3298_ = lean_unsigned_to_nat(1u);
v___x_3299_ = lean_nat_add(v_i_3256_, v___x_3298_);
lean_dec(v_i_3256_);
v_i_3256_ = v___x_3299_;
goto _start;
}
}
}
v___jp_3282_:
{
lean_object* v_size_3284_; uint8_t v___x_3285_; 
v_size_3284_ = lean_ctor_get(v_a_u2082_3254_, 2);
v___x_3285_ = lean_nat_dec_lt(v_j_3257_, v_size_3284_);
if (v___x_3285_ == 0)
{
lean_dec(v_val_3281_);
lean_dec(v_j_3257_);
lean_dec(v_i_3256_);
return v___y_3283_;
}
else
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3276_, v_a_u2082_3254_, v_j_3257_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
lean_dec(v_val_3281_);
v___x_3287_ = lean_unsigned_to_nat(1u);
v___x_3288_ = lean_nat_add(v_j_3257_, v___x_3287_);
lean_dec(v_j_3257_);
v_j_3257_ = v___x_3288_;
goto _start;
}
else
{
lean_object* v_val_3290_; lean_object* v_fvarId_3291_; 
v_val_3290_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_val_3290_);
lean_dec_ref_known(v___x_3286_, 1);
v_fvarId_3291_ = lean_ctor_get(v_val_3281_, 1);
lean_inc(v_fvarId_3291_);
lean_dec(v_val_3281_);
v___y_3270_ = v_val_3290_;
v___y_3271_ = v_fvarId_3291_;
goto v___jp_3269_;
}
}
}
}
}
v___jp_3258_:
{
uint8_t v___x_3261_; 
v___x_3261_ = l_Lean_instBEqFVarId_beq(v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec(v___y_3259_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = lean_unsigned_to_nat(1u);
v___x_3263_ = lean_nat_add(v_j_3257_, v___x_3262_);
lean_dec(v_j_3257_);
v_j_3257_ = v___x_3263_;
goto _start;
}
else
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = lean_unsigned_to_nat(1u);
v___x_3266_ = lean_nat_add(v_i_3256_, v___x_3265_);
lean_dec(v_i_3256_);
v___x_3267_ = lean_nat_add(v_j_3257_, v___x_3265_);
lean_dec(v_j_3257_);
v_i_3256_ = v___x_3266_;
v_j_3257_ = v___x_3267_;
goto _start;
}
}
v___jp_3269_:
{
lean_object* v_fvarId_3272_; 
v_fvarId_3272_ = lean_ctor_get(v___y_3270_, 1);
lean_inc(v_fvarId_3272_);
lean_dec_ref(v___y_3270_);
v___y_3259_ = v___y_3271_;
v___y_3260_ = v_fvarId_3272_;
goto v___jp_3258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3301_, lean_object* v_a_u2082_3302_, lean_object* v_exceptFVars_3303_, lean_object* v_i_3304_, lean_object* v_j_3305_){
_start:
{
uint8_t v_res_3306_; lean_object* v_r_3307_; 
v_res_3306_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3301_, v_a_u2082_3302_, v_exceptFVars_3303_, v_i_3304_, v_j_3305_);
lean_dec_ref(v_exceptFVars_3303_);
lean_dec_ref(v_a_u2082_3302_);
lean_dec_ref(v_a_u2081_3301_);
v_r_3307_ = lean_box(v_res_3306_);
return v_r_3307_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3308_, lean_object* v_lctx_u2082_3309_, lean_object* v_exceptFVars_3310_){
_start:
{
lean_object* v_decls_3311_; lean_object* v_decls_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v_decls_3311_ = lean_ctor_get(v_lctx_u2081_3308_, 1);
v_decls_3312_ = lean_ctor_get(v_lctx_u2082_3309_, 1);
v___x_3313_ = lean_unsigned_to_nat(0u);
v___x_3314_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3311_, v_decls_3312_, v_exceptFVars_3310_, v___x_3313_, v___x_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3315_, lean_object* v_lctx_u2082_3316_, lean_object* v_exceptFVars_3317_){
_start:
{
uint8_t v_res_3318_; lean_object* v_r_3319_; 
v_res_3318_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3315_, v_lctx_u2082_3316_, v_exceptFVars_3317_);
lean_dec_ref(v_exceptFVars_3317_);
lean_dec_ref(v_lctx_u2082_3316_);
lean_dec_ref(v_lctx_u2081_3315_);
v_r_3319_ = lean_box(v_res_3318_);
return v_r_3319_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3321_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3322_ = lean_unsigned_to_nat(14u);
v___x_3323_ = lean_unsigned_to_nat(576u);
v___x_3324_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3325_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3326_ = l_mkPanicMessageWithDecl(v___x_3325_, v___x_3324_, v___x_3323_, v___x_3322_, v___x_3321_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3327_, lean_object* v_lctx_3328_, lean_object* v___x_3329_, uint8_t v_isLambda_3330_, uint8_t v_usedLetOnly_3331_, uint8_t v_generalizeNondepLet_3332_, lean_object* v_i_3333_, lean_object* v_x_3334_, lean_object* v_b_3335_){
_start:
{
lean_object* v_n_3337_; lean_object* v_ty_3338_; uint8_t v_bi_3339_; lean_object* v_x_3343_; lean_object* v___x_3344_; 
v_x_3343_ = lean_array_fget_borrowed(v_xs_3327_, v_i_3333_);
v___x_3344_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3328_, v_x_3343_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
lean_dec_ref(v_b_3335_);
v___x_3345_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3346_ = l_panic___redArg(v___x_3329_, v___x_3345_);
return v___x_3346_;
}
else
{
lean_object* v_val_3347_; 
v_val_3347_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_val_3347_);
lean_dec_ref_known(v___x_3344_, 1);
if (lean_obj_tag(v_val_3347_) == 0)
{
lean_object* v_userName_3348_; lean_object* v_type_3349_; uint8_t v_bi_3350_; 
v_userName_3348_ = lean_ctor_get(v_val_3347_, 2);
lean_inc(v_userName_3348_);
v_type_3349_ = lean_ctor_get(v_val_3347_, 3);
lean_inc_ref(v_type_3349_);
v_bi_3350_ = lean_ctor_get_uint8(v_val_3347_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3347_, 4);
v_n_3337_ = v_userName_3348_;
v_ty_3338_ = v_type_3349_;
v_bi_3339_ = v_bi_3350_;
goto v___jp_3336_;
}
else
{
lean_object* v_userName_3351_; lean_object* v_type_3352_; lean_object* v_value_3353_; uint8_t v_nondep_3354_; 
v_userName_3351_ = lean_ctor_get(v_val_3347_, 2);
lean_inc(v_userName_3351_);
v_type_3352_ = lean_ctor_get(v_val_3347_, 3);
lean_inc_ref(v_type_3352_);
v_value_3353_ = lean_ctor_get(v_val_3347_, 4);
lean_inc_ref(v_value_3353_);
v_nondep_3354_ = lean_ctor_get_uint8(v_val_3347_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3347_, 5);
if (v_nondep_3354_ == 0)
{
goto v___jp_3359_;
}
else
{
if (v_generalizeNondepLet_3332_ == 0)
{
goto v___jp_3359_;
}
else
{
uint8_t v___x_3365_; 
lean_dec_ref(v_value_3353_);
v___x_3365_ = 0;
v_n_3337_ = v_userName_3351_;
v_ty_3338_ = v_type_3352_;
v_bi_3339_ = v___x_3365_;
goto v___jp_3336_;
}
}
v___jp_3355_:
{
lean_object* v_ty_3356_; lean_object* v_val_3357_; lean_object* v___x_3358_; 
v_ty_3356_ = lean_expr_abstract_range(v_type_3352_, v_i_3333_, v_xs_3327_);
lean_dec_ref(v_type_3352_);
v_val_3357_ = lean_expr_abstract_range(v_value_3353_, v_i_3333_, v_xs_3327_);
lean_dec_ref(v_value_3353_);
v___x_3358_ = l_Lean_Expr_letE___override(v_userName_3351_, v_ty_3356_, v_val_3357_, v_b_3335_, v_nondep_3354_);
return v___x_3358_;
}
v___jp_3359_:
{
uint8_t v___x_3360_; 
v___x_3360_ = lean_bool_not(v_usedLetOnly_3331_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3361_ = lean_unsigned_to_nat(0u);
v___x_3362_ = lean_expr_has_loose_bvar(v_b_3335_, v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec_ref(v_value_3353_);
lean_dec_ref(v_type_3352_);
lean_dec(v_userName_3351_);
v___x_3363_ = lean_unsigned_to_nat(1u);
v___x_3364_ = lean_expr_lower_loose_bvars(v_b_3335_, v___x_3363_, v___x_3363_);
lean_dec_ref(v_b_3335_);
return v___x_3364_;
}
else
{
goto v___jp_3355_;
}
}
else
{
goto v___jp_3355_;
}
}
}
}
v___jp_3336_:
{
lean_object* v_ty_3340_; 
v_ty_3340_ = lean_expr_abstract_range(v_ty_3338_, v_i_3333_, v_xs_3327_);
lean_dec_ref(v_ty_3338_);
if (v_isLambda_3330_ == 0)
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Lean_mkForall(v_n_3337_, v_bi_3339_, v_ty_3340_, v_b_3335_);
return v___x_3341_;
}
else
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_mkLambda(v_n_3337_, v_bi_3339_, v_ty_3340_, v_b_3335_);
return v___x_3342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3366_, lean_object* v_lctx_3367_, lean_object* v___x_3368_, lean_object* v_isLambda_3369_, lean_object* v_usedLetOnly_3370_, lean_object* v_generalizeNondepLet_3371_, lean_object* v_i_3372_, lean_object* v_x_3373_, lean_object* v_b_3374_){
_start:
{
uint8_t v_isLambda_boxed_3375_; uint8_t v_usedLetOnly_boxed_3376_; uint8_t v_generalizeNondepLet_boxed_3377_; lean_object* v_res_3378_; 
v_isLambda_boxed_3375_ = lean_unbox(v_isLambda_3369_);
v_usedLetOnly_boxed_3376_ = lean_unbox(v_usedLetOnly_3370_);
v_generalizeNondepLet_boxed_3377_ = lean_unbox(v_generalizeNondepLet_3371_);
v_res_3378_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3366_, v_lctx_3367_, v___x_3368_, v_isLambda_boxed_3375_, v_usedLetOnly_boxed_3376_, v_generalizeNondepLet_boxed_3377_, v_i_3372_, v_x_3373_, v_b_3374_);
lean_dec(v_i_3372_);
lean_dec_ref(v___x_3368_);
lean_dec_ref(v_xs_3366_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3379_, lean_object* v_lctx_3380_, lean_object* v_xs_3381_, lean_object* v_b_3382_, uint8_t v_usedLetOnly_3383_, uint8_t v_generalizeNondepLet_3384_){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___f_3389_; lean_object* v_b_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3385_ = l_Lean_instInhabitedExpr;
v___x_3386_ = lean_box(v_isLambda_3379_);
v___x_3387_ = lean_box(v_usedLetOnly_3383_);
v___x_3388_ = lean_box(v_generalizeNondepLet_3384_);
lean_inc_ref(v_xs_3381_);
v___f_3389_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3389_, 0, v_xs_3381_);
lean_closure_set(v___f_3389_, 1, v_lctx_3380_);
lean_closure_set(v___f_3389_, 2, v___x_3385_);
lean_closure_set(v___f_3389_, 3, v___x_3386_);
lean_closure_set(v___f_3389_, 4, v___x_3387_);
lean_closure_set(v___f_3389_, 5, v___x_3388_);
v_b_3390_ = lean_expr_abstract(v_b_3382_, v_xs_3381_);
v___x_3391_ = lean_array_get_size(v_xs_3381_);
lean_dec_ref(v_xs_3381_);
v___x_3392_ = l_Nat_foldRev___redArg(v___x_3391_, v___f_3389_, v_b_3390_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3393_, lean_object* v_lctx_3394_, lean_object* v_xs_3395_, lean_object* v_b_3396_, lean_object* v_usedLetOnly_3397_, lean_object* v_generalizeNondepLet_3398_){
_start:
{
uint8_t v_isLambda_boxed_3399_; uint8_t v_usedLetOnly_boxed_3400_; uint8_t v_generalizeNondepLet_boxed_3401_; lean_object* v_res_3402_; 
v_isLambda_boxed_3399_ = lean_unbox(v_isLambda_3393_);
v_usedLetOnly_boxed_3400_ = lean_unbox(v_usedLetOnly_3397_);
v_generalizeNondepLet_boxed_3401_ = lean_unbox(v_generalizeNondepLet_3398_);
v_res_3402_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3399_, v_lctx_3394_, v_xs_3395_, v_b_3396_, v_usedLetOnly_boxed_3400_, v_generalizeNondepLet_boxed_3401_);
lean_dec_ref(v_b_3396_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3403_, lean_object* v_lctx_3404_, uint8_t v_usedLetOnly_3405_, uint8_t v_generalizeNondepLet_3406_, lean_object* v_x_3407_, lean_object* v_x_3408_){
_start:
{
lean_object* v_zero_3409_; uint8_t v_isZero_3410_; 
v_zero_3409_ = lean_unsigned_to_nat(0u);
v_isZero_3410_ = lean_nat_dec_eq(v_x_3407_, v_zero_3409_);
if (v_isZero_3410_ == 1)
{
lean_dec(v_x_3407_);
lean_dec_ref(v_lctx_3404_);
return v_x_3408_;
}
else
{
lean_object* v_one_3411_; lean_object* v_n_3412_; lean_object* v_n_3414_; lean_object* v_ty_3415_; uint8_t v_bi_3416_; lean_object* v_x_3420_; lean_object* v___x_3421_; 
v_one_3411_ = lean_unsigned_to_nat(1u);
v_n_3412_ = lean_nat_sub(v_x_3407_, v_one_3411_);
lean_dec(v_x_3407_);
v_x_3420_ = lean_array_fget_borrowed(v_xs_3403_, v_n_3412_);
lean_inc_ref(v_lctx_3404_);
v___x_3421_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3404_, v_x_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_dec_ref(v_x_3408_);
v___x_3422_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3423_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3422_);
v_x_3407_ = v_n_3412_;
v_x_3408_ = v___x_3423_;
goto _start;
}
else
{
lean_object* v_val_3425_; 
v_val_3425_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_val_3425_);
lean_dec_ref_known(v___x_3421_, 1);
if (lean_obj_tag(v_val_3425_) == 0)
{
lean_object* v_userName_3426_; lean_object* v_type_3427_; uint8_t v_bi_3428_; 
v_userName_3426_ = lean_ctor_get(v_val_3425_, 2);
lean_inc(v_userName_3426_);
v_type_3427_ = lean_ctor_get(v_val_3425_, 3);
lean_inc_ref(v_type_3427_);
v_bi_3428_ = lean_ctor_get_uint8(v_val_3425_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3425_, 4);
v_n_3414_ = v_userName_3426_;
v_ty_3415_ = v_type_3427_;
v_bi_3416_ = v_bi_3428_;
goto v___jp_3413_;
}
else
{
lean_object* v_userName_3429_; lean_object* v_type_3430_; lean_object* v_value_3431_; uint8_t v_nondep_3432_; 
v_userName_3429_ = lean_ctor_get(v_val_3425_, 2);
lean_inc(v_userName_3429_);
v_type_3430_ = lean_ctor_get(v_val_3425_, 3);
lean_inc_ref(v_type_3430_);
v_value_3431_ = lean_ctor_get(v_val_3425_, 4);
lean_inc_ref(v_value_3431_);
v_nondep_3432_ = lean_ctor_get_uint8(v_val_3425_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3425_, 5);
if (v_nondep_3432_ == 0)
{
goto v___jp_3438_;
}
else
{
if (v_generalizeNondepLet_3406_ == 0)
{
goto v___jp_3438_;
}
else
{
uint8_t v___x_3443_; 
lean_dec_ref(v_value_3431_);
v___x_3443_ = 0;
v_n_3414_ = v_userName_3429_;
v_ty_3415_ = v_type_3430_;
v_bi_3416_ = v___x_3443_;
goto v___jp_3413_;
}
}
v___jp_3433_:
{
lean_object* v_ty_3434_; lean_object* v_val_3435_; lean_object* v___x_3436_; 
v_ty_3434_ = lean_expr_abstract_range(v_type_3430_, v_n_3412_, v_xs_3403_);
lean_dec_ref(v_type_3430_);
v_val_3435_ = lean_expr_abstract_range(v_value_3431_, v_n_3412_, v_xs_3403_);
lean_dec_ref(v_value_3431_);
v___x_3436_ = l_Lean_Expr_letE___override(v_userName_3429_, v_ty_3434_, v_val_3435_, v_x_3408_, v_nondep_3432_);
v_x_3407_ = v_n_3412_;
v_x_3408_ = v___x_3436_;
goto _start;
}
v___jp_3438_:
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_bool_not(v_usedLetOnly_3405_);
if (v___x_3439_ == 0)
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_expr_has_loose_bvar(v_x_3408_, v_zero_3409_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; 
lean_dec_ref(v_value_3431_);
lean_dec_ref(v_type_3430_);
lean_dec(v_userName_3429_);
v___x_3441_ = lean_expr_lower_loose_bvars(v_x_3408_, v_one_3411_, v_one_3411_);
lean_dec_ref(v_x_3408_);
v_x_3407_ = v_n_3412_;
v_x_3408_ = v___x_3441_;
goto _start;
}
else
{
goto v___jp_3433_;
}
}
else
{
goto v___jp_3433_;
}
}
}
}
v___jp_3413_:
{
lean_object* v_ty_3417_; lean_object* v___x_3418_; 
v_ty_3417_ = lean_expr_abstract_range(v_ty_3415_, v_n_3412_, v_xs_3403_);
lean_dec_ref(v_ty_3415_);
v___x_3418_ = l_Lean_mkLambda(v_n_3414_, v_bi_3416_, v_ty_3417_, v_x_3408_);
v_x_3407_ = v_n_3412_;
v_x_3408_ = v___x_3418_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3444_, lean_object* v_lctx_3445_, lean_object* v_usedLetOnly_3446_, lean_object* v_generalizeNondepLet_3447_, lean_object* v_x_3448_, lean_object* v_x_3449_){
_start:
{
uint8_t v_usedLetOnly_boxed_3450_; uint8_t v_generalizeNondepLet_boxed_3451_; lean_object* v_res_3452_; 
v_usedLetOnly_boxed_3450_ = lean_unbox(v_usedLetOnly_3446_);
v_generalizeNondepLet_boxed_3451_ = lean_unbox(v_generalizeNondepLet_3447_);
v_res_3452_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3444_, v_lctx_3445_, v_usedLetOnly_boxed_3450_, v_generalizeNondepLet_boxed_3451_, v_x_3448_, v_x_3449_);
lean_dec_ref(v_xs_3444_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3453_, lean_object* v_lctx_3454_, uint8_t v_usedLetOnly_3455_, uint8_t v_generalizeNondepLet_3456_, lean_object* v_x_3457_, lean_object* v_x_3458_){
_start:
{
lean_object* v_zero_3459_; uint8_t v_isZero_3460_; 
v_zero_3459_ = lean_unsigned_to_nat(0u);
v_isZero_3460_ = lean_nat_dec_eq(v_x_3457_, v_zero_3459_);
if (v_isZero_3460_ == 1)
{
lean_dec_ref(v_lctx_3454_);
return v_x_3458_;
}
else
{
lean_object* v_one_3461_; lean_object* v_n_3462_; lean_object* v_n_3464_; lean_object* v_ty_3465_; uint8_t v_bi_3466_; lean_object* v_x_3470_; lean_object* v___x_3471_; 
v_one_3461_ = lean_unsigned_to_nat(1u);
v_n_3462_ = lean_nat_sub(v_x_3457_, v_one_3461_);
v_x_3470_ = lean_array_fget_borrowed(v_xs_3453_, v_n_3462_);
lean_inc_ref(v_lctx_3454_);
v___x_3471_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3454_, v_x_3470_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
lean_dec_ref(v_x_3458_);
v___x_3472_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3473_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3472_);
v___x_3474_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3453_, v_lctx_3454_, v_usedLetOnly_3455_, v_generalizeNondepLet_3456_, v_n_3462_, v___x_3473_);
return v___x_3474_;
}
else
{
lean_object* v_val_3475_; 
v_val_3475_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_val_3475_);
lean_dec_ref_known(v___x_3471_, 1);
if (lean_obj_tag(v_val_3475_) == 0)
{
lean_object* v_userName_3476_; lean_object* v_type_3477_; uint8_t v_bi_3478_; 
v_userName_3476_ = lean_ctor_get(v_val_3475_, 2);
lean_inc(v_userName_3476_);
v_type_3477_ = lean_ctor_get(v_val_3475_, 3);
lean_inc_ref(v_type_3477_);
v_bi_3478_ = lean_ctor_get_uint8(v_val_3475_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3475_, 4);
v_n_3464_ = v_userName_3476_;
v_ty_3465_ = v_type_3477_;
v_bi_3466_ = v_bi_3478_;
goto v___jp_3463_;
}
else
{
lean_object* v_userName_3479_; lean_object* v_type_3480_; lean_object* v_value_3481_; uint8_t v_nondep_3482_; 
v_userName_3479_ = lean_ctor_get(v_val_3475_, 2);
lean_inc(v_userName_3479_);
v_type_3480_ = lean_ctor_get(v_val_3475_, 3);
lean_inc_ref(v_type_3480_);
v_value_3481_ = lean_ctor_get(v_val_3475_, 4);
lean_inc_ref(v_value_3481_);
v_nondep_3482_ = lean_ctor_get_uint8(v_val_3475_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3475_, 5);
if (v_nondep_3482_ == 0)
{
goto v___jp_3488_;
}
else
{
if (v_generalizeNondepLet_3456_ == 0)
{
goto v___jp_3488_;
}
else
{
uint8_t v___x_3493_; 
lean_dec_ref(v_value_3481_);
v___x_3493_ = 0;
v_n_3464_ = v_userName_3479_;
v_ty_3465_ = v_type_3480_;
v_bi_3466_ = v___x_3493_;
goto v___jp_3463_;
}
}
v___jp_3483_:
{
lean_object* v_ty_3484_; lean_object* v_val_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_ty_3484_ = lean_expr_abstract_range(v_type_3480_, v_n_3462_, v_xs_3453_);
lean_dec_ref(v_type_3480_);
v_val_3485_ = lean_expr_abstract_range(v_value_3481_, v_n_3462_, v_xs_3453_);
lean_dec_ref(v_value_3481_);
v___x_3486_ = l_Lean_Expr_letE___override(v_userName_3479_, v_ty_3484_, v_val_3485_, v_x_3458_, v_nondep_3482_);
v___x_3487_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3453_, v_lctx_3454_, v_usedLetOnly_3455_, v_generalizeNondepLet_3456_, v_n_3462_, v___x_3486_);
return v___x_3487_;
}
v___jp_3488_:
{
uint8_t v___x_3489_; 
v___x_3489_ = lean_bool_not(v_usedLetOnly_3455_);
if (v___x_3489_ == 0)
{
uint8_t v___x_3490_; 
v___x_3490_ = lean_expr_has_loose_bvar(v_x_3458_, v_zero_3459_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
lean_dec_ref(v_value_3481_);
lean_dec_ref(v_type_3480_);
lean_dec(v_userName_3479_);
v___x_3491_ = lean_expr_lower_loose_bvars(v_x_3458_, v_one_3461_, v_one_3461_);
lean_dec_ref(v_x_3458_);
v___x_3492_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3453_, v_lctx_3454_, v_usedLetOnly_3455_, v_generalizeNondepLet_3456_, v_n_3462_, v___x_3491_);
return v___x_3492_;
}
else
{
goto v___jp_3483_;
}
}
else
{
goto v___jp_3483_;
}
}
}
}
v___jp_3463_:
{
lean_object* v_ty_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v_ty_3467_ = lean_expr_abstract_range(v_ty_3465_, v_n_3462_, v_xs_3453_);
lean_dec_ref(v_ty_3465_);
v___x_3468_ = l_Lean_mkLambda(v_n_3464_, v_bi_3466_, v_ty_3467_, v_x_3458_);
v___x_3469_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3453_, v_lctx_3454_, v_usedLetOnly_3455_, v_generalizeNondepLet_3456_, v_n_3462_, v___x_3468_);
return v___x_3469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3494_, lean_object* v_lctx_3495_, lean_object* v_usedLetOnly_3496_, lean_object* v_generalizeNondepLet_3497_, lean_object* v_x_3498_, lean_object* v_x_3499_){
_start:
{
uint8_t v_usedLetOnly_boxed_3500_; uint8_t v_generalizeNondepLet_boxed_3501_; lean_object* v_res_3502_; 
v_usedLetOnly_boxed_3500_ = lean_unbox(v_usedLetOnly_3496_);
v_generalizeNondepLet_boxed_3501_ = lean_unbox(v_generalizeNondepLet_3497_);
v_res_3502_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3494_, v_lctx_3495_, v_usedLetOnly_boxed_3500_, v_generalizeNondepLet_boxed_3501_, v_x_3498_, v_x_3499_);
lean_dec(v_x_3498_);
lean_dec_ref(v_xs_3494_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3503_, lean_object* v_xs_3504_, lean_object* v_b_3505_, uint8_t v_usedLetOnly_3506_, uint8_t v_generalizeNondepLet_3507_){
_start:
{
lean_object* v_b_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v_b_3508_ = lean_expr_abstract(v_b_3505_, v_xs_3504_);
v___x_3509_ = lean_array_get_size(v_xs_3504_);
v___x_3510_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3504_, v_lctx_3503_, v_usedLetOnly_3506_, v_generalizeNondepLet_3507_, v___x_3509_, v_b_3508_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3511_, lean_object* v_xs_3512_, lean_object* v_b_3513_, lean_object* v_usedLetOnly_3514_, lean_object* v_generalizeNondepLet_3515_){
_start:
{
uint8_t v_usedLetOnly_boxed_3516_; uint8_t v_generalizeNondepLet_boxed_3517_; lean_object* v_res_3518_; 
v_usedLetOnly_boxed_3516_ = lean_unbox(v_usedLetOnly_3514_);
v_generalizeNondepLet_boxed_3517_ = lean_unbox(v_generalizeNondepLet_3515_);
v_res_3518_ = l_Lean_LocalContext_mkLambda(v_lctx_3511_, v_xs_3512_, v_b_3513_, v_usedLetOnly_boxed_3516_, v_generalizeNondepLet_boxed_3517_);
lean_dec_ref(v_b_3513_);
lean_dec_ref(v_xs_3512_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3519_, lean_object* v_lctx_3520_, uint8_t v_usedLetOnly_3521_, uint8_t v_generalizeNondepLet_3522_, lean_object* v_x_3523_, lean_object* v_x_3524_){
_start:
{
lean_object* v_zero_3525_; uint8_t v_isZero_3526_; 
v_zero_3525_ = lean_unsigned_to_nat(0u);
v_isZero_3526_ = lean_nat_dec_eq(v_x_3523_, v_zero_3525_);
if (v_isZero_3526_ == 1)
{
lean_dec(v_x_3523_);
lean_dec_ref(v_lctx_3520_);
return v_x_3524_;
}
else
{
lean_object* v_one_3527_; lean_object* v_n_3528_; lean_object* v_n_3530_; lean_object* v_ty_3531_; uint8_t v_bi_3532_; lean_object* v_x_3536_; lean_object* v___x_3537_; 
v_one_3527_ = lean_unsigned_to_nat(1u);
v_n_3528_ = lean_nat_sub(v_x_3523_, v_one_3527_);
lean_dec(v_x_3523_);
v_x_3536_ = lean_array_fget_borrowed(v_xs_3519_, v_n_3528_);
lean_inc_ref(v_lctx_3520_);
v___x_3537_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3520_, v_x_3536_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
lean_dec_ref(v_x_3524_);
v___x_3538_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3539_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3538_);
v_x_3523_ = v_n_3528_;
v_x_3524_ = v___x_3539_;
goto _start;
}
else
{
lean_object* v_val_3541_; 
v_val_3541_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_val_3541_);
lean_dec_ref_known(v___x_3537_, 1);
if (lean_obj_tag(v_val_3541_) == 0)
{
lean_object* v_userName_3542_; lean_object* v_type_3543_; uint8_t v_bi_3544_; 
v_userName_3542_ = lean_ctor_get(v_val_3541_, 2);
lean_inc(v_userName_3542_);
v_type_3543_ = lean_ctor_get(v_val_3541_, 3);
lean_inc_ref(v_type_3543_);
v_bi_3544_ = lean_ctor_get_uint8(v_val_3541_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3541_, 4);
v_n_3530_ = v_userName_3542_;
v_ty_3531_ = v_type_3543_;
v_bi_3532_ = v_bi_3544_;
goto v___jp_3529_;
}
else
{
lean_object* v_userName_3545_; lean_object* v_type_3546_; lean_object* v_value_3547_; uint8_t v_nondep_3548_; 
v_userName_3545_ = lean_ctor_get(v_val_3541_, 2);
lean_inc(v_userName_3545_);
v_type_3546_ = lean_ctor_get(v_val_3541_, 3);
lean_inc_ref(v_type_3546_);
v_value_3547_ = lean_ctor_get(v_val_3541_, 4);
lean_inc_ref(v_value_3547_);
v_nondep_3548_ = lean_ctor_get_uint8(v_val_3541_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3541_, 5);
if (v_nondep_3548_ == 0)
{
goto v___jp_3554_;
}
else
{
if (v_generalizeNondepLet_3522_ == 0)
{
goto v___jp_3554_;
}
else
{
uint8_t v___x_3559_; 
lean_dec_ref(v_value_3547_);
v___x_3559_ = 0;
v_n_3530_ = v_userName_3545_;
v_ty_3531_ = v_type_3546_;
v_bi_3532_ = v___x_3559_;
goto v___jp_3529_;
}
}
v___jp_3549_:
{
lean_object* v_ty_3550_; lean_object* v_val_3551_; lean_object* v___x_3552_; 
v_ty_3550_ = lean_expr_abstract_range(v_type_3546_, v_n_3528_, v_xs_3519_);
lean_dec_ref(v_type_3546_);
v_val_3551_ = lean_expr_abstract_range(v_value_3547_, v_n_3528_, v_xs_3519_);
lean_dec_ref(v_value_3547_);
v___x_3552_ = l_Lean_Expr_letE___override(v_userName_3545_, v_ty_3550_, v_val_3551_, v_x_3524_, v_nondep_3548_);
v_x_3523_ = v_n_3528_;
v_x_3524_ = v___x_3552_;
goto _start;
}
v___jp_3554_:
{
uint8_t v___x_3555_; 
v___x_3555_ = lean_bool_not(v_usedLetOnly_3521_);
if (v___x_3555_ == 0)
{
uint8_t v___x_3556_; 
v___x_3556_ = lean_expr_has_loose_bvar(v_x_3524_, v_zero_3525_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; 
lean_dec_ref(v_value_3547_);
lean_dec_ref(v_type_3546_);
lean_dec(v_userName_3545_);
v___x_3557_ = lean_expr_lower_loose_bvars(v_x_3524_, v_one_3527_, v_one_3527_);
lean_dec_ref(v_x_3524_);
v_x_3523_ = v_n_3528_;
v_x_3524_ = v___x_3557_;
goto _start;
}
else
{
goto v___jp_3549_;
}
}
else
{
goto v___jp_3549_;
}
}
}
}
v___jp_3529_:
{
lean_object* v_ty_3533_; lean_object* v___x_3534_; 
v_ty_3533_ = lean_expr_abstract_range(v_ty_3531_, v_n_3528_, v_xs_3519_);
lean_dec_ref(v_ty_3531_);
v___x_3534_ = l_Lean_mkForall(v_n_3530_, v_bi_3532_, v_ty_3533_, v_x_3524_);
v_x_3523_ = v_n_3528_;
v_x_3524_ = v___x_3534_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3560_, lean_object* v_lctx_3561_, lean_object* v_usedLetOnly_3562_, lean_object* v_generalizeNondepLet_3563_, lean_object* v_x_3564_, lean_object* v_x_3565_){
_start:
{
uint8_t v_usedLetOnly_boxed_3566_; uint8_t v_generalizeNondepLet_boxed_3567_; lean_object* v_res_3568_; 
v_usedLetOnly_boxed_3566_ = lean_unbox(v_usedLetOnly_3562_);
v_generalizeNondepLet_boxed_3567_ = lean_unbox(v_generalizeNondepLet_3563_);
v_res_3568_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3560_, v_lctx_3561_, v_usedLetOnly_boxed_3566_, v_generalizeNondepLet_boxed_3567_, v_x_3564_, v_x_3565_);
lean_dec_ref(v_xs_3560_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3569_, lean_object* v_lctx_3570_, uint8_t v_usedLetOnly_3571_, uint8_t v_generalizeNondepLet_3572_, lean_object* v_x_3573_, lean_object* v_x_3574_){
_start:
{
lean_object* v_zero_3575_; uint8_t v_isZero_3576_; 
v_zero_3575_ = lean_unsigned_to_nat(0u);
v_isZero_3576_ = lean_nat_dec_eq(v_x_3573_, v_zero_3575_);
if (v_isZero_3576_ == 1)
{
lean_dec_ref(v_lctx_3570_);
return v_x_3574_;
}
else
{
lean_object* v_one_3577_; lean_object* v_n_3578_; lean_object* v_n_3580_; lean_object* v_ty_3581_; uint8_t v_bi_3582_; lean_object* v_x_3586_; lean_object* v___x_3587_; 
v_one_3577_ = lean_unsigned_to_nat(1u);
v_n_3578_ = lean_nat_sub(v_x_3573_, v_one_3577_);
v_x_3586_ = lean_array_fget_borrowed(v_xs_3569_, v_n_3578_);
lean_inc_ref(v_lctx_3570_);
v___x_3587_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3570_, v_x_3586_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_dec_ref(v_x_3574_);
v___x_3588_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3589_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3588_);
v___x_3590_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3569_, v_lctx_3570_, v_usedLetOnly_3571_, v_generalizeNondepLet_3572_, v_n_3578_, v___x_3589_);
return v___x_3590_;
}
else
{
lean_object* v_val_3591_; 
v_val_3591_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_val_3591_);
lean_dec_ref_known(v___x_3587_, 1);
if (lean_obj_tag(v_val_3591_) == 0)
{
lean_object* v_userName_3592_; lean_object* v_type_3593_; uint8_t v_bi_3594_; 
v_userName_3592_ = lean_ctor_get(v_val_3591_, 2);
lean_inc(v_userName_3592_);
v_type_3593_ = lean_ctor_get(v_val_3591_, 3);
lean_inc_ref(v_type_3593_);
v_bi_3594_ = lean_ctor_get_uint8(v_val_3591_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3591_, 4);
v_n_3580_ = v_userName_3592_;
v_ty_3581_ = v_type_3593_;
v_bi_3582_ = v_bi_3594_;
goto v___jp_3579_;
}
else
{
lean_object* v_userName_3595_; lean_object* v_type_3596_; lean_object* v_value_3597_; uint8_t v_nondep_3598_; 
v_userName_3595_ = lean_ctor_get(v_val_3591_, 2);
lean_inc(v_userName_3595_);
v_type_3596_ = lean_ctor_get(v_val_3591_, 3);
lean_inc_ref(v_type_3596_);
v_value_3597_ = lean_ctor_get(v_val_3591_, 4);
lean_inc_ref(v_value_3597_);
v_nondep_3598_ = lean_ctor_get_uint8(v_val_3591_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3591_, 5);
if (v_nondep_3598_ == 0)
{
goto v___jp_3604_;
}
else
{
if (v_generalizeNondepLet_3572_ == 0)
{
goto v___jp_3604_;
}
else
{
uint8_t v___x_3609_; 
lean_dec_ref(v_value_3597_);
v___x_3609_ = 0;
v_n_3580_ = v_userName_3595_;
v_ty_3581_ = v_type_3596_;
v_bi_3582_ = v___x_3609_;
goto v___jp_3579_;
}
}
v___jp_3599_:
{
lean_object* v_ty_3600_; lean_object* v_val_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_ty_3600_ = lean_expr_abstract_range(v_type_3596_, v_n_3578_, v_xs_3569_);
lean_dec_ref(v_type_3596_);
v_val_3601_ = lean_expr_abstract_range(v_value_3597_, v_n_3578_, v_xs_3569_);
lean_dec_ref(v_value_3597_);
v___x_3602_ = l_Lean_Expr_letE___override(v_userName_3595_, v_ty_3600_, v_val_3601_, v_x_3574_, v_nondep_3598_);
v___x_3603_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3569_, v_lctx_3570_, v_usedLetOnly_3571_, v_generalizeNondepLet_3572_, v_n_3578_, v___x_3602_);
return v___x_3603_;
}
v___jp_3604_:
{
uint8_t v___x_3605_; 
v___x_3605_ = lean_bool_not(v_usedLetOnly_3571_);
if (v___x_3605_ == 0)
{
uint8_t v___x_3606_; 
v___x_3606_ = lean_expr_has_loose_bvar(v_x_3574_, v_zero_3575_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
lean_dec_ref(v_value_3597_);
lean_dec_ref(v_type_3596_);
lean_dec(v_userName_3595_);
v___x_3607_ = lean_expr_lower_loose_bvars(v_x_3574_, v_one_3577_, v_one_3577_);
lean_dec_ref(v_x_3574_);
v___x_3608_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3569_, v_lctx_3570_, v_usedLetOnly_3571_, v_generalizeNondepLet_3572_, v_n_3578_, v___x_3607_);
return v___x_3608_;
}
else
{
goto v___jp_3599_;
}
}
else
{
goto v___jp_3599_;
}
}
}
}
v___jp_3579_:
{
lean_object* v_ty_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v_ty_3583_ = lean_expr_abstract_range(v_ty_3581_, v_n_3578_, v_xs_3569_);
lean_dec_ref(v_ty_3581_);
v___x_3584_ = l_Lean_mkForall(v_n_3580_, v_bi_3582_, v_ty_3583_, v_x_3574_);
v___x_3585_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3569_, v_lctx_3570_, v_usedLetOnly_3571_, v_generalizeNondepLet_3572_, v_n_3578_, v___x_3584_);
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3610_, lean_object* v_lctx_3611_, lean_object* v_usedLetOnly_3612_, lean_object* v_generalizeNondepLet_3613_, lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
uint8_t v_usedLetOnly_boxed_3616_; uint8_t v_generalizeNondepLet_boxed_3617_; lean_object* v_res_3618_; 
v_usedLetOnly_boxed_3616_ = lean_unbox(v_usedLetOnly_3612_);
v_generalizeNondepLet_boxed_3617_ = lean_unbox(v_generalizeNondepLet_3613_);
v_res_3618_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3610_, v_lctx_3611_, v_usedLetOnly_boxed_3616_, v_generalizeNondepLet_boxed_3617_, v_x_3614_, v_x_3615_);
lean_dec(v_x_3614_);
lean_dec_ref(v_xs_3610_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3619_, lean_object* v_xs_3620_, lean_object* v_b_3621_, uint8_t v_usedLetOnly_3622_, uint8_t v_generalizeNondepLet_3623_){
_start:
{
lean_object* v_b_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v_b_3624_ = lean_expr_abstract(v_b_3621_, v_xs_3620_);
v___x_3625_ = lean_array_get_size(v_xs_3620_);
v___x_3626_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3620_, v_lctx_3619_, v_usedLetOnly_3622_, v_generalizeNondepLet_3623_, v___x_3625_, v_b_3624_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3627_, lean_object* v_xs_3628_, lean_object* v_b_3629_, lean_object* v_usedLetOnly_3630_, lean_object* v_generalizeNondepLet_3631_){
_start:
{
uint8_t v_usedLetOnly_boxed_3632_; uint8_t v_generalizeNondepLet_boxed_3633_; lean_object* v_res_3634_; 
v_usedLetOnly_boxed_3632_ = lean_unbox(v_usedLetOnly_3630_);
v_generalizeNondepLet_boxed_3633_ = lean_unbox(v_generalizeNondepLet_3631_);
v_res_3634_ = l_Lean_LocalContext_mkForall(v_lctx_3627_, v_xs_3628_, v_b_3629_, v_usedLetOnly_boxed_3632_, v_generalizeNondepLet_boxed_3633_);
lean_dec_ref(v_b_3629_);
lean_dec_ref(v_xs_3628_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3635_, lean_object* v_p_3636_, lean_object* v_d_3637_){
_start:
{
if (lean_obj_tag(v_d_3637_) == 0)
{
uint8_t v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
lean_dec(v_p_3636_);
v___x_3638_ = 0;
v___x_3639_ = lean_box(v___x_3638_);
v___x_3640_ = lean_apply_2(v_toPure_3635_, lean_box(0), v___x_3639_);
return v___x_3640_;
}
else
{
lean_object* v_val_3641_; lean_object* v___x_3642_; 
lean_dec(v_toPure_3635_);
v_val_3641_ = lean_ctor_get(v_d_3637_, 0);
lean_inc(v_val_3641_);
lean_dec_ref_known(v_d_3637_, 1);
v___x_3642_ = lean_apply_1(v_p_3636_, v_val_3641_);
return v___x_3642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3643_, lean_object* v_lctx_3644_, lean_object* v_p_3645_){
_start:
{
lean_object* v_toApplicative_3646_; lean_object* v_decls_3647_; lean_object* v_toPure_3648_; lean_object* v___f_3649_; lean_object* v___x_3650_; 
v_toApplicative_3646_ = lean_ctor_get(v_inst_3643_, 0);
v_decls_3647_ = lean_ctor_get(v_lctx_3644_, 1);
lean_inc_ref(v_decls_3647_);
lean_dec_ref(v_lctx_3644_);
v_toPure_3648_ = lean_ctor_get(v_toApplicative_3646_, 1);
lean_inc(v_toPure_3648_);
v___f_3649_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3649_, 0, v_toPure_3648_);
lean_closure_set(v___f_3649_, 1, v_p_3645_);
v___x_3650_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3643_, v_decls_3647_, v___f_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3651_, lean_object* v_inst_3652_, lean_object* v_lctx_3653_, lean_object* v_p_3654_){
_start:
{
lean_object* v_toApplicative_3655_; lean_object* v_decls_3656_; lean_object* v_toPure_3657_; lean_object* v___f_3658_; lean_object* v___x_3659_; 
v_toApplicative_3655_ = lean_ctor_get(v_inst_3652_, 0);
v_decls_3656_ = lean_ctor_get(v_lctx_3653_, 1);
lean_inc_ref(v_decls_3656_);
lean_dec_ref(v_lctx_3653_);
v_toPure_3657_ = lean_ctor_get(v_toApplicative_3655_, 1);
lean_inc(v_toPure_3657_);
v___f_3658_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3658_, 0, v_toPure_3657_);
lean_closure_set(v___f_3658_, 1, v_p_3654_);
v___x_3659_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3652_, v_decls_3656_, v___f_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3660_, uint8_t v_b_3661_){
_start:
{
uint8_t v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = lean_bool_not(v_b_3661_);
v___x_3663_ = lean_box(v___x_3662_);
v___x_3664_ = lean_apply_2(v_toPure_3660_, lean_box(0), v___x_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3665_, lean_object* v_b_3666_){
_start:
{
uint8_t v_b_boxed_3667_; lean_object* v_res_3668_; 
v_b_boxed_3667_ = lean_unbox(v_b_3666_);
v_res_3668_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3665_, v_b_boxed_3667_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3669_, lean_object* v_toBind_3670_, lean_object* v___f_3671_, lean_object* v_p_3672_, lean_object* v_v_3673_){
_start:
{
if (lean_obj_tag(v_v_3673_) == 0)
{
uint8_t v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
lean_dec(v_p_3672_);
v___x_3674_ = 1;
v___x_3675_ = lean_box(v___x_3674_);
v___x_3676_ = lean_apply_2(v_toPure_3669_, lean_box(0), v___x_3675_);
v___x_3677_ = lean_apply_4(v_toBind_3670_, lean_box(0), lean_box(0), v___x_3676_, v___f_3671_);
return v___x_3677_;
}
else
{
lean_object* v_val_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
lean_dec(v_toPure_3669_);
v_val_3678_ = lean_ctor_get(v_v_3673_, 0);
lean_inc(v_val_3678_);
lean_dec_ref_known(v_v_3673_, 1);
v___x_3679_ = lean_apply_1(v_p_3672_, v_val_3678_);
v___x_3680_ = lean_apply_4(v_toBind_3670_, lean_box(0), lean_box(0), v___x_3679_, v___f_3671_);
return v___x_3680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3681_, lean_object* v_lctx_3682_, lean_object* v_p_3683_){
_start:
{
lean_object* v_toApplicative_3684_; lean_object* v_decls_3685_; lean_object* v_toBind_3686_; lean_object* v_toPure_3687_; lean_object* v___f_3688_; lean_object* v___f_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v_toApplicative_3684_ = lean_ctor_get(v_inst_3681_, 0);
v_decls_3685_ = lean_ctor_get(v_lctx_3682_, 1);
lean_inc_ref(v_decls_3685_);
lean_dec_ref(v_lctx_3682_);
v_toBind_3686_ = lean_ctor_get(v_inst_3681_, 1);
lean_inc_n(v_toBind_3686_, 2);
v_toPure_3687_ = lean_ctor_get(v_toApplicative_3684_, 1);
lean_inc_n(v_toPure_3687_, 2);
v___f_3688_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3688_, 0, v_toPure_3687_);
lean_inc_ref(v___f_3688_);
v___f_3689_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3689_, 0, v_toPure_3687_);
lean_closure_set(v___f_3689_, 1, v_toBind_3686_);
lean_closure_set(v___f_3689_, 2, v___f_3688_);
lean_closure_set(v___f_3689_, 3, v_p_3683_);
v___x_3690_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3681_, v_decls_3685_, v___f_3689_);
v___x_3691_ = lean_apply_4(v_toBind_3686_, lean_box(0), lean_box(0), v___x_3690_, v___f_3688_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3692_, lean_object* v_inst_3693_, lean_object* v_lctx_3694_, lean_object* v_p_3695_){
_start:
{
lean_object* v_toApplicative_3696_; lean_object* v_decls_3697_; lean_object* v_toBind_3698_; lean_object* v_toPure_3699_; lean_object* v___f_3700_; lean_object* v___f_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v_toApplicative_3696_ = lean_ctor_get(v_inst_3693_, 0);
v_decls_3697_ = lean_ctor_get(v_lctx_3694_, 1);
lean_inc_ref(v_decls_3697_);
lean_dec_ref(v_lctx_3694_);
v_toBind_3698_ = lean_ctor_get(v_inst_3693_, 1);
lean_inc_n(v_toBind_3698_, 2);
v_toPure_3699_ = lean_ctor_get(v_toApplicative_3696_, 1);
lean_inc_n(v_toPure_3699_, 2);
v___f_3700_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3700_, 0, v_toPure_3699_);
lean_inc_ref(v___f_3700_);
v___f_3701_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3701_, 0, v_toPure_3699_);
lean_closure_set(v___f_3701_, 1, v_toBind_3698_);
lean_closure_set(v___f_3701_, 2, v___f_3700_);
lean_closure_set(v___f_3701_, 3, v_p_3695_);
v___x_3702_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3693_, v_decls_3697_, v___f_3701_);
v___x_3703_ = lean_apply_4(v_toBind_3698_, lean_box(0), lean_box(0), v___x_3702_, v___f_3700_);
return v___x_3703_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3704_, lean_object* v_d_3705_){
_start:
{
if (lean_obj_tag(v_d_3705_) == 0)
{
uint8_t v___x_3706_; 
lean_dec_ref(v_p_3704_);
v___x_3706_ = 0;
return v___x_3706_;
}
else
{
lean_object* v_val_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; 
v_val_3707_ = lean_ctor_get(v_d_3705_, 0);
lean_inc(v_val_3707_);
lean_dec_ref_known(v_d_3705_, 1);
v___x_3708_ = lean_apply_1(v_p_3704_, v_val_3707_);
v___x_3709_ = lean_unbox(v___x_3708_);
return v___x_3709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3710_, lean_object* v_d_3711_){
_start:
{
uint8_t v_res_3712_; lean_object* v_r_3713_; 
v_res_3712_ = l_Lean_LocalContext_any___lam__0(v_p_3710_, v_d_3711_);
v_r_3713_ = lean_box(v_res_3712_);
return v_r_3713_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3714_, lean_object* v_p_3715_){
_start:
{
lean_object* v___x_3716_; lean_object* v_decls_3717_; lean_object* v___f_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v___x_3716_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3717_ = lean_ctor_get(v_lctx_3714_, 1);
lean_inc_ref(v_decls_3717_);
lean_dec_ref(v_lctx_3714_);
v___f_3718_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3718_, 0, v_p_3715_);
v___x_3719_ = l_Lean_PersistentArray_anyM___redArg(v___x_3716_, v_decls_3717_, v___f_3718_);
v___x_3720_ = lean_unbox(v___x_3719_);
lean_dec(v___x_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3721_, lean_object* v_p_3722_){
_start:
{
uint8_t v_res_3723_; lean_object* v_r_3724_; 
v_res_3723_ = l_Lean_LocalContext_any(v_lctx_3721_, v_p_3722_);
v_r_3724_ = lean_box(v_res_3723_);
return v_r_3724_;
}
}
static uint8_t _init_l_Lean_LocalContext_all___lam__0___closed__0(void){
_start:
{
uint8_t v___x_3725_; uint8_t v___x_3726_; 
v___x_3725_ = 1;
v___x_3726_ = lean_bool_not(v___x_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3727_, lean_object* v_v_3728_){
_start:
{
if (lean_obj_tag(v_v_3728_) == 0)
{
uint8_t v___x_3729_; 
lean_dec_ref(v_p_3727_);
v___x_3729_ = lean_uint8_once(&l_Lean_LocalContext_all___lam__0___closed__0, &l_Lean_LocalContext_all___lam__0___closed__0_once, _init_l_Lean_LocalContext_all___lam__0___closed__0);
return v___x_3729_;
}
else
{
lean_object* v_val_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; uint8_t v___x_3733_; 
v_val_3730_ = lean_ctor_get(v_v_3728_, 0);
lean_inc(v_val_3730_);
lean_dec_ref_known(v_v_3728_, 1);
v___x_3731_ = lean_apply_1(v_p_3727_, v_val_3730_);
v___x_3732_ = lean_unbox(v___x_3731_);
v___x_3733_ = lean_bool_not(v___x_3732_);
return v___x_3733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3734_, lean_object* v_v_3735_){
_start:
{
uint8_t v_res_3736_; lean_object* v_r_3737_; 
v_res_3736_ = l_Lean_LocalContext_all___lam__0(v_p_3734_, v_v_3735_);
v_r_3737_ = lean_box(v_res_3736_);
return v_r_3737_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3738_, lean_object* v_p_3739_){
_start:
{
lean_object* v___x_3740_; lean_object* v_decls_3741_; lean_object* v___f_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; uint8_t v___x_3745_; 
v___x_3740_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3741_ = lean_ctor_get(v_lctx_3738_, 1);
lean_inc_ref(v_decls_3741_);
lean_dec_ref(v_lctx_3738_);
v___f_3742_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3742_, 0, v_p_3739_);
v___x_3743_ = l_Lean_PersistentArray_anyM___redArg(v___x_3740_, v_decls_3741_, v___f_3742_);
v___x_3744_ = lean_unbox(v___x_3743_);
lean_dec(v___x_3743_);
v___x_3745_ = lean_bool_not(v___x_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3746_, lean_object* v_p_3747_){
_start:
{
uint8_t v_res_3748_; lean_object* v_r_3749_; 
v_res_3748_ = l_Lean_LocalContext_all(v_lctx_3746_, v_p_3747_);
v_r_3749_ = lean_box(v_res_3748_);
return v_r_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3750_, lean_object* v_a_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_zero_3754_; uint8_t v_isZero_3755_; 
v_zero_3754_ = lean_unsigned_to_nat(0u);
v_isZero_3755_ = lean_nat_dec_eq(v_i_3750_, v_zero_3754_);
if (v_isZero_3755_ == 1)
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
lean_dec(v_i_3750_);
v___x_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3756_, 0, v_a_3751_);
lean_ctor_set(v___x_3756_, 1, v___y_3752_);
v___x_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set(v___x_3757_, 1, v___y_3753_);
return v___x_3757_;
}
else
{
lean_object* v_decls_3758_; lean_object* v_size_3759_; lean_object* v_one_3760_; lean_object* v_n_3761_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3778_; lean_object* v___y_3779_; uint8_t v___y_3780_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3790_; lean_object* v___x_3794_; uint8_t v___x_3795_; 
v_decls_3758_ = lean_ctor_get(v_a_3751_, 1);
v_size_3759_ = lean_ctor_get(v_decls_3758_, 2);
v_one_3760_ = lean_unsigned_to_nat(1u);
v_n_3761_ = lean_nat_sub(v_i_3750_, v_one_3760_);
lean_dec(v_i_3750_);
v___x_3794_ = lean_box(0);
v___x_3795_ = lean_nat_dec_lt(v_n_3761_, v_size_3759_);
if (v___x_3795_ == 0)
{
lean_object* v___x_3796_; 
v___x_3796_ = l_outOfBounds___redArg(v___x_3794_);
v___y_3790_ = v___x_3796_;
goto v___jp_3789_;
}
else
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3794_, v_decls_3758_, v_n_3761_);
v___y_3790_ = v___x_3797_;
goto v___jp_3789_;
}
v___jp_3762_:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_LocalContext_setUserName(v_a_3751_, v___y_3766_, v___y_3764_);
v_i_3750_ = v_n_3761_;
v_a_3751_ = v___x_3767_;
v___y_3752_ = v___y_3763_;
v___y_3753_ = v___y_3765_;
goto _start;
}
v___jp_3769_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v_fst_3774_; lean_object* v_snd_3775_; lean_object* v_fvarId_3776_; 
lean_inc(v___y_3771_);
v___x_3772_ = l_Lean_NameSet_insert(v___y_3752_, v___y_3771_);
v___x_3773_ = l_Lean_sanitizeName(v___y_3771_, v___y_3753_);
v_fst_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_fst_3774_);
v_snd_3775_ = lean_ctor_get(v___x_3773_, 1);
lean_inc(v_snd_3775_);
lean_dec_ref(v___x_3773_);
v_fvarId_3776_ = lean_ctor_get(v___y_3770_, 1);
lean_inc(v_fvarId_3776_);
lean_dec_ref(v___y_3770_);
v___y_3763_ = v___x_3772_;
v___y_3764_ = v_fst_3774_;
v___y_3765_ = v_snd_3775_;
v___y_3766_ = v_fvarId_3776_;
goto v___jp_3762_;
}
v___jp_3777_:
{
if (v___y_3780_ == 0)
{
lean_object* v___x_3781_; 
lean_dec_ref(v___y_3778_);
v___x_3781_ = l_Lean_NameSet_insert(v___y_3752_, v___y_3779_);
v_i_3750_ = v_n_3761_;
v___y_3752_ = v___x_3781_;
goto _start;
}
else
{
v___y_3770_ = v___y_3778_;
v___y_3771_ = v___y_3779_;
goto v___jp_3769_;
}
}
v___jp_3783_:
{
uint8_t v___x_3786_; 
v___x_3786_ = l_Lean_Name_hasMacroScopes(v___y_3785_);
if (v___x_3786_ == 0)
{
lean_object* v_userName_3787_; uint8_t v___x_3788_; 
v_userName_3787_ = lean_ctor_get(v___y_3784_, 2);
v___x_3788_ = l_Lean_NameSet_contains(v___y_3752_, v_userName_3787_);
v___y_3778_ = v___y_3784_;
v___y_3779_ = v___y_3785_;
v___y_3780_ = v___x_3788_;
goto v___jp_3777_;
}
else
{
v___y_3770_ = v___y_3784_;
v___y_3771_ = v___y_3785_;
goto v___jp_3769_;
}
}
v___jp_3789_:
{
if (lean_obj_tag(v___y_3790_) == 0)
{
v_i_3750_ = v_n_3761_;
goto _start;
}
else
{
lean_object* v_val_3792_; lean_object* v_userName_3793_; 
v_val_3792_ = lean_ctor_get(v___y_3790_, 0);
lean_inc(v_val_3792_);
lean_dec_ref_known(v___y_3790_, 1);
v_userName_3793_ = lean_ctor_get(v_val_3792_, 2);
lean_inc(v_userName_3793_);
v___y_3784_ = v_val_3792_;
v___y_3785_ = v_userName_3793_;
goto v___jp_3783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3798_, lean_object* v_a_3799_){
_start:
{
lean_object* v_options_3800_; uint8_t v___x_3801_; uint8_t v___x_3802_; 
v_options_3800_ = lean_ctor_get(v_a_3799_, 0);
v___x_3801_ = l_Lean_getSanitizeNames(v_options_3800_);
v___x_3802_ = lean_bool_not(v___x_3801_);
if (v___x_3802_ == 0)
{
lean_object* v_decls_3803_; lean_object* v_size_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v_fst_3807_; lean_object* v_snd_3808_; lean_object* v_fst_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
v_decls_3803_ = lean_ctor_get(v_lctx_3798_, 1);
v_size_3804_ = lean_ctor_get(v_decls_3803_, 2);
lean_inc(v_size_3804_);
v___x_3805_ = l_Lean_NameSet_empty;
v___x_3806_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3804_, v_lctx_3798_, v___x_3805_, v_a_3799_);
v_fst_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_fst_3807_);
v_snd_3808_ = lean_ctor_get(v___x_3806_, 1);
lean_inc(v_snd_3808_);
lean_dec_ref(v___x_3806_);
v_fst_3809_ = lean_ctor_get(v_fst_3807_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_fst_3807_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; 
v_unused_3817_ = lean_ctor_get(v_fst_3807_, 1);
lean_dec(v_unused_3817_);
v___x_3811_ = v_fst_3807_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_fst_3809_);
lean_dec(v_fst_3807_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 1, v_snd_3808_);
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_fst_3809_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_snd_3808_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
else
{
lean_object* v___x_3818_; 
v___x_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3818_, 0, v_lctx_3798_);
lean_ctor_set(v___x_3818_, 1, v_a_3799_);
return v___x_3818_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3819_, lean_object* v_i_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3820_, v_a_3822_, v___y_3823_, v___y_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3826_, lean_object* v_i_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3826_, v_i_3827_, v_a_3828_, v_a_3829_, v___y_3830_, v___y_3831_);
lean_dec(v_n_3826_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3833_, lean_object* v_fvarId_3834_){
_start:
{
lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___x_3847_; 
lean_inc_ref(v_lctx_3833_);
v___x_3847_ = lean_local_ctx_find(v_lctx_3833_, v_fvarId_3834_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v___x_3848_; 
lean_dec_ref(v_lctx_3833_);
v___x_3848_ = lean_box(0);
return v___x_3848_;
}
else
{
lean_object* v_val_3849_; lean_object* v___y_3851_; lean_object* v_userName_3856_; 
v_val_3849_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_val_3849_);
lean_dec_ref_known(v___x_3847_, 1);
v_userName_3856_ = lean_ctor_get(v_val_3849_, 2);
lean_inc(v_userName_3856_);
v___y_3851_ = v_userName_3856_;
goto v___jp_3850_;
v___jp_3850_:
{
lean_object* v___x_3852_; 
v___x_3852_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3833_, v___y_3851_);
lean_dec_ref(v_lctx_3833_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v___x_3853_; 
lean_dec(v___y_3851_);
lean_dec(v_val_3849_);
v___x_3853_ = lean_box(0);
return v___x_3853_;
}
else
{
lean_object* v_val_3854_; lean_object* v_fvarId_3855_; 
v_val_3854_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_val_3854_);
lean_dec_ref_known(v___x_3852_, 1);
v_fvarId_3855_ = lean_ctor_get(v_val_3849_, 1);
lean_inc(v_fvarId_3855_);
lean_dec(v_val_3849_);
v___y_3843_ = v_val_3854_;
v___y_3844_ = v___y_3851_;
v___y_3845_ = v_fvarId_3855_;
goto v___jp_3842_;
}
}
}
v___jp_3835_:
{
uint8_t v___x_3839_; 
v___x_3839_ = l_Lean_instBEqFVarId_beq(v___y_3836_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec(v___y_3836_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; 
lean_dec(v___y_3837_);
v___x_3840_ = lean_box(0);
return v___x_3840_;
}
else
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___y_3837_);
return v___x_3841_;
}
}
v___jp_3842_:
{
lean_object* v_fvarId_3846_; 
v_fvarId_3846_ = lean_ctor_get(v___y_3843_, 1);
lean_inc(v_fvarId_3846_);
lean_dec_ref(v___y_3843_);
v___y_3836_ = v___y_3845_;
v___y_3837_ = v___y_3844_;
v___y_3838_ = v_fvarId_3846_;
goto v___jp_3835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3857_, size_t v_i_3858_, lean_object* v_bs_3859_){
_start:
{
uint8_t v___x_3860_; 
v___x_3860_ = lean_usize_dec_lt(v_i_3858_, v_sz_3857_);
if (v___x_3860_ == 0)
{
return v_bs_3859_;
}
else
{
lean_object* v_v_3861_; lean_object* v_snd_3862_; lean_object* v___x_3863_; lean_object* v_bs_x27_3864_; size_t v___x_3865_; size_t v___x_3866_; lean_object* v___x_3867_; 
v_v_3861_ = lean_array_uget_borrowed(v_bs_3859_, v_i_3858_);
v_snd_3862_ = lean_ctor_get(v_v_3861_, 1);
lean_inc(v_snd_3862_);
v___x_3863_ = lean_unsigned_to_nat(0u);
v_bs_x27_3864_ = lean_array_uset(v_bs_3859_, v_i_3858_, v___x_3863_);
v___x_3865_ = ((size_t)1ULL);
v___x_3866_ = lean_usize_add(v_i_3858_, v___x_3865_);
v___x_3867_ = lean_array_uset(v_bs_x27_3864_, v_i_3858_, v_snd_3862_);
v_i_3858_ = v___x_3866_;
v_bs_3859_ = v___x_3867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3869_, lean_object* v_i_3870_, lean_object* v_bs_3871_){
_start:
{
size_t v_sz_boxed_3872_; size_t v_i_boxed_3873_; lean_object* v_res_3874_; 
v_sz_boxed_3872_ = lean_unbox_usize(v_sz_3869_);
lean_dec(v_sz_3869_);
v_i_boxed_3873_ = lean_unbox_usize(v_i_3870_);
lean_dec(v_i_3870_);
v_res_3874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3872_, v_i_boxed_3873_, v_bs_3871_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3875_, size_t v_sz_3876_, size_t v_i_3877_, lean_object* v_bs_3878_){
_start:
{
uint8_t v___x_3879_; 
v___x_3879_ = lean_usize_dec_lt(v_i_3877_, v_sz_3876_);
if (v___x_3879_ == 0)
{
return v_bs_3878_;
}
else
{
lean_object* v_fvarIdToDecl_3880_; lean_object* v_v_3881_; lean_object* v___x_3882_; lean_object* v_bs_x27_3883_; lean_object* v___y_3885_; lean_object* v___x_3890_; 
v_fvarIdToDecl_3880_ = lean_ctor_get(v_lctx_3875_, 0);
v_v_3881_ = lean_array_uget(v_bs_3878_, v_i_3877_);
v___x_3882_ = lean_unsigned_to_nat(0u);
v_bs_x27_3883_ = lean_array_uset(v_bs_3878_, v_i_3877_, v___x_3882_);
v___x_3890_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3880_, v_v_3881_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v___x_3891_; 
v___x_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3882_);
lean_ctor_set(v___x_3891_, 1, v_v_3881_);
v___y_3885_ = v___x_3891_;
goto v___jp_3884_;
}
else
{
lean_object* v_val_3892_; lean_object* v_index_3893_; lean_object* v___x_3894_; 
v_val_3892_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_val_3892_);
lean_dec_ref_known(v___x_3890_, 1);
v_index_3893_ = lean_ctor_get(v_val_3892_, 0);
lean_inc(v_index_3893_);
lean_dec(v_val_3892_);
v___x_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3894_, 0, v_index_3893_);
lean_ctor_set(v___x_3894_, 1, v_v_3881_);
v___y_3885_ = v___x_3894_;
goto v___jp_3884_;
}
v___jp_3884_:
{
size_t v___x_3886_; size_t v___x_3887_; lean_object* v___x_3888_; 
v___x_3886_ = ((size_t)1ULL);
v___x_3887_ = lean_usize_add(v_i_3877_, v___x_3886_);
v___x_3888_ = lean_array_uset(v_bs_x27_3883_, v_i_3877_, v___y_3885_);
v_i_3877_ = v___x_3887_;
v_bs_3878_ = v___x_3888_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3895_, lean_object* v_sz_3896_, lean_object* v_i_3897_, lean_object* v_bs_3898_){
_start:
{
size_t v_sz_boxed_3899_; size_t v_i_boxed_3900_; lean_object* v_res_3901_; 
v_sz_boxed_3899_ = lean_unbox_usize(v_sz_3896_);
lean_dec(v_sz_3896_);
v_i_boxed_3900_ = lean_unbox_usize(v_i_3897_);
lean_dec(v_i_3897_);
v_res_3901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3895_, v_sz_boxed_3899_, v_i_boxed_3900_, v_bs_3898_);
lean_dec_ref(v_lctx_3895_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object* v_hi_3902_, lean_object* v_pivot_3903_, lean_object* v_as_3904_, lean_object* v_i_3905_, lean_object* v_k_3906_){
_start:
{
uint8_t v___x_3907_; 
v___x_3907_ = lean_nat_dec_lt(v_k_3906_, v_hi_3902_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_dec(v_k_3906_);
v___x_3908_ = lean_array_fswap(v_as_3904_, v_i_3905_, v_hi_3902_);
v___x_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3909_, 0, v_i_3905_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
return v___x_3909_;
}
else
{
lean_object* v___x_3910_; lean_object* v_fst_3911_; lean_object* v_fst_3912_; uint8_t v___x_3913_; 
v___x_3910_ = lean_array_fget_borrowed(v_as_3904_, v_k_3906_);
v_fst_3911_ = lean_ctor_get(v___x_3910_, 0);
v_fst_3912_ = lean_ctor_get(v_pivot_3903_, 0);
v___x_3913_ = lean_nat_dec_lt(v_fst_3911_, v_fst_3912_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3914_ = lean_unsigned_to_nat(1u);
v___x_3915_ = lean_nat_add(v_k_3906_, v___x_3914_);
lean_dec(v_k_3906_);
v_k_3906_ = v___x_3915_;
goto _start;
}
else
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3917_ = lean_array_fswap(v_as_3904_, v_i_3905_, v_k_3906_);
v___x_3918_ = lean_unsigned_to_nat(1u);
v___x_3919_ = lean_nat_add(v_i_3905_, v___x_3918_);
lean_dec(v_i_3905_);
v___x_3920_ = lean_nat_add(v_k_3906_, v___x_3918_);
lean_dec(v_k_3906_);
v_as_3904_ = v___x_3917_;
v_i_3905_ = v___x_3919_;
v_k_3906_ = v___x_3920_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object* v_hi_3922_, lean_object* v_pivot_3923_, lean_object* v_as_3924_, lean_object* v_i_3925_, lean_object* v_k_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3922_, v_pivot_3923_, v_as_3924_, v_i_3925_, v_k_3926_);
lean_dec_ref(v_pivot_3923_);
lean_dec(v_hi_3922_);
return v_res_3927_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3928_, lean_object* v_i_3929_){
_start:
{
lean_object* v_fst_3930_; lean_object* v_fst_3931_; uint8_t v___x_3932_; 
v_fst_3930_ = lean_ctor_get(v_h_3928_, 0);
v_fst_3931_ = lean_ctor_get(v_i_3929_, 0);
v___x_3932_ = lean_nat_dec_lt(v_fst_3930_, v_fst_3931_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3933_, lean_object* v_i_3934_){
_start:
{
uint8_t v_res_3935_; lean_object* v_r_3936_; 
v_res_3935_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3933_, v_i_3934_);
lean_dec_ref(v_i_3934_);
lean_dec_ref(v_h_3933_);
v_r_3936_ = lean_box(v_res_3935_);
return v_r_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_n_3937_, lean_object* v_as_3938_, lean_object* v_lo_3939_, lean_object* v_hi_3940_){
_start:
{
lean_object* v___y_3942_; uint8_t v___x_3952_; 
v___x_3952_ = lean_nat_dec_lt(v_lo_3939_, v_hi_3940_);
if (v___x_3952_ == 0)
{
lean_dec(v_lo_3939_);
return v_as_3938_;
}
else
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v_mid_3955_; lean_object* v___y_3957_; lean_object* v___y_3963_; lean_object* v___x_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; 
v___x_3953_ = lean_nat_add(v_lo_3939_, v_hi_3940_);
v___x_3954_ = lean_unsigned_to_nat(1u);
v_mid_3955_ = lean_nat_shiftr(v___x_3953_, v___x_3954_);
lean_dec(v___x_3953_);
v___x_3968_ = lean_array_fget_borrowed(v_as_3938_, v_mid_3955_);
v___x_3969_ = lean_array_fget_borrowed(v_as_3938_, v_lo_3939_);
v___x_3970_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3968_, v___x_3969_);
if (v___x_3970_ == 0)
{
v___y_3963_ = v_as_3938_;
goto v___jp_3962_;
}
else
{
lean_object* v___x_3971_; 
v___x_3971_ = lean_array_fswap(v_as_3938_, v_lo_3939_, v_mid_3955_);
v___y_3963_ = v___x_3971_;
goto v___jp_3962_;
}
v___jp_3956_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v___x_3958_ = lean_array_fget_borrowed(v___y_3957_, v_mid_3955_);
v___x_3959_ = lean_array_fget_borrowed(v___y_3957_, v_hi_3940_);
v___x_3960_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3958_, v___x_3959_);
if (v___x_3960_ == 0)
{
lean_dec(v_mid_3955_);
v___y_3942_ = v___y_3957_;
goto v___jp_3941_;
}
else
{
lean_object* v___x_3961_; 
v___x_3961_ = lean_array_fswap(v___y_3957_, v_mid_3955_, v_hi_3940_);
lean_dec(v_mid_3955_);
v___y_3942_ = v___x_3961_;
goto v___jp_3941_;
}
}
v___jp_3962_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v___x_3964_ = lean_array_fget_borrowed(v___y_3963_, v_hi_3940_);
v___x_3965_ = lean_array_fget_borrowed(v___y_3963_, v_lo_3939_);
v___x_3966_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3964_, v___x_3965_);
if (v___x_3966_ == 0)
{
v___y_3957_ = v___y_3963_;
goto v___jp_3956_;
}
else
{
lean_object* v___x_3967_; 
v___x_3967_ = lean_array_fswap(v___y_3963_, v_lo_3939_, v_hi_3940_);
v___y_3957_ = v___x_3967_;
goto v___jp_3956_;
}
}
}
v___jp_3941_:
{
lean_object* v_pivot_3943_; lean_object* v___x_3944_; lean_object* v_fst_3945_; lean_object* v_snd_3946_; uint8_t v___x_3947_; 
v_pivot_3943_ = lean_array_fget(v___y_3942_, v_hi_3940_);
lean_inc_n(v_lo_3939_, 2);
v___x_3944_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3940_, v_pivot_3943_, v___y_3942_, v_lo_3939_, v_lo_3939_);
lean_dec(v_pivot_3943_);
v_fst_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_fst_3945_);
v_snd_3946_ = lean_ctor_get(v___x_3944_, 1);
lean_inc(v_snd_3946_);
lean_dec_ref(v___x_3944_);
v___x_3947_ = lean_nat_dec_le(v_hi_3940_, v_fst_3945_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3948_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3937_, v_snd_3946_, v_lo_3939_, v_fst_3945_);
v___x_3949_ = lean_unsigned_to_nat(1u);
v___x_3950_ = lean_nat_add(v_fst_3945_, v___x_3949_);
lean_dec(v_fst_3945_);
v_as_3938_ = v___x_3948_;
v_lo_3939_ = v___x_3950_;
goto _start;
}
else
{
lean_dec(v_fst_3945_);
lean_dec(v_lo_3939_);
return v_snd_3946_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_n_3972_, lean_object* v_as_3973_, lean_object* v_lo_3974_, lean_object* v_hi_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3972_, v_as_3973_, v_lo_3974_, v_hi_3975_);
lean_dec(v_hi_3975_);
lean_dec(v_n_3972_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3977_, lean_object* v_hyps_3978_){
_start:
{
lean_object* v___y_3980_; size_t v_sz_3984_; size_t v___x_3985_; lean_object* v_hyps_3986_; lean_object* v___x_3987_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___x_3992_; uint8_t v___x_3993_; 
v_sz_3984_ = lean_array_size(v_hyps_3978_);
v___x_3985_ = ((size_t)0ULL);
v_hyps_3986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3977_, v_sz_3984_, v___x_3985_, v_hyps_3978_);
v___x_3987_ = lean_array_get_size(v_hyps_3986_);
v___x_3992_ = lean_unsigned_to_nat(0u);
v___x_3993_ = lean_nat_dec_eq(v___x_3987_, v___x_3992_);
if (v___x_3993_ == 0)
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___y_3997_; uint8_t v___x_3999_; 
v___x_3994_ = lean_unsigned_to_nat(1u);
v___x_3995_ = lean_nat_sub(v___x_3987_, v___x_3994_);
v___x_3999_ = lean_nat_dec_le(v___x_3992_, v___x_3995_);
if (v___x_3999_ == 0)
{
lean_inc(v___x_3995_);
v___y_3997_ = v___x_3995_;
goto v___jp_3996_;
}
else
{
v___y_3997_ = v___x_3992_;
goto v___jp_3996_;
}
v___jp_3996_:
{
uint8_t v___x_3998_; 
v___x_3998_ = lean_nat_dec_le(v___y_3997_, v___x_3995_);
if (v___x_3998_ == 0)
{
lean_dec(v___x_3995_);
lean_inc(v___y_3997_);
v___y_3989_ = v___y_3997_;
v___y_3990_ = v___y_3997_;
goto v___jp_3988_;
}
else
{
v___y_3989_ = v___y_3997_;
v___y_3990_ = v___x_3995_;
goto v___jp_3988_;
}
}
}
else
{
v___y_3980_ = v_hyps_3986_;
goto v___jp_3979_;
}
v___jp_3979_:
{
size_t v_sz_3981_; size_t v___x_3982_; lean_object* v___x_3983_; 
v_sz_3981_ = lean_array_size(v___y_3980_);
v___x_3982_ = ((size_t)0ULL);
v___x_3983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3981_, v___x_3982_, v___y_3980_);
return v___x_3983_;
}
v___jp_3988_:
{
lean_object* v___x_3991_; 
v___x_3991_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v___x_3987_, v_hyps_3986_, v___y_3989_, v___y_3990_);
lean_dec(v___y_3990_);
v___y_3980_ = v___x_3991_;
goto v___jp_3979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object* v_lctx_4000_, lean_object* v_hyps_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_4000_, v_hyps_4001_);
lean_dec_ref(v_lctx_4000_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_4003_, lean_object* v_as_4004_, lean_object* v_lo_4005_, lean_object* v_hi_4006_, lean_object* v_w_4007_, lean_object* v_hlo_4008_, lean_object* v_hhi_4009_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_4003_, v_as_4004_, v_lo_4005_, v_hi_4006_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_4011_, lean_object* v_as_4012_, lean_object* v_lo_4013_, lean_object* v_hi_4014_, lean_object* v_w_4015_, lean_object* v_hlo_4016_, lean_object* v_hhi_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_4011_, v_as_4012_, v_lo_4013_, v_hi_4014_, v_w_4015_, v_hlo_4016_, v_hhi_4017_);
lean_dec(v_hi_4014_);
lean_dec(v_n_4011_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object* v_n_4019_, lean_object* v_lo_4020_, lean_object* v_hi_4021_, lean_object* v_hhi_4022_, lean_object* v_pivot_4023_, lean_object* v_as_4024_, lean_object* v_i_4025_, lean_object* v_k_4026_, lean_object* v_ilo_4027_, lean_object* v_ik_4028_, lean_object* v_w_4029_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_4021_, v_pivot_4023_, v_as_4024_, v_i_4025_, v_k_4026_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object* v_n_4031_, lean_object* v_lo_4032_, lean_object* v_hi_4033_, lean_object* v_hhi_4034_, lean_object* v_pivot_4035_, lean_object* v_as_4036_, lean_object* v_i_4037_, lean_object* v_k_4038_, lean_object* v_ilo_4039_, lean_object* v_ik_4040_, lean_object* v_w_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(v_n_4031_, v_lo_4032_, v_hi_4033_, v_hhi_4034_, v_pivot_4035_, v_as_4036_, v_i_4037_, v_k_4038_, v_ilo_4039_, v_ik_4040_, v_w_4041_);
lean_dec_ref(v_pivot_4035_);
lean_dec(v_hi_4033_);
lean_dec(v_lo_4032_);
lean_dec(v_n_4031_);
return v_res_4042_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_4043_, lean_object* v_x_4044_){
_start:
{
if (lean_obj_tag(v_x_4044_) == 0)
{
uint8_t v___x_4045_; 
v___x_4045_ = 0;
return v___x_4045_;
}
else
{
lean_object* v_key_4046_; lean_object* v_tail_4047_; uint8_t v___x_4048_; 
v_key_4046_ = lean_ctor_get(v_x_4044_, 0);
v_tail_4047_ = lean_ctor_get(v_x_4044_, 2);
v___x_4048_ = lean_name_eq(v_key_4046_, v_a_4043_);
if (v___x_4048_ == 0)
{
v_x_4044_ = v_tail_4047_;
goto _start;
}
else
{
return v___x_4048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_4050_, lean_object* v_x_4051_){
_start:
{
uint8_t v_res_4052_; lean_object* v_r_4053_; 
v_res_4052_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4050_, v_x_4051_);
lean_dec(v_x_4051_);
lean_dec(v_a_4050_);
v_r_4053_ = lean_box(v_res_4052_);
return v_r_4053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_4054_, lean_object* v_x_4055_){
_start:
{
if (lean_obj_tag(v_x_4055_) == 0)
{
return v_x_4055_;
}
else
{
lean_object* v_key_4056_; lean_object* v_value_4057_; lean_object* v_tail_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4067_; 
v_key_4056_ = lean_ctor_get(v_x_4055_, 0);
v_value_4057_ = lean_ctor_get(v_x_4055_, 1);
v_tail_4058_ = lean_ctor_get(v_x_4055_, 2);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_x_4055_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4060_ = v_x_4055_;
v_isShared_4061_ = v_isSharedCheck_4067_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_tail_4058_);
lean_inc(v_value_4057_);
lean_inc(v_key_4056_);
lean_dec(v_x_4055_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4067_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
uint8_t v___x_4062_; 
v___x_4062_ = lean_name_eq(v_key_4056_, v_a_4054_);
if (v___x_4062_ == 0)
{
lean_object* v___x_4063_; lean_object* v___x_4065_; 
v___x_4063_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4054_, v_tail_4058_);
if (v_isShared_4061_ == 0)
{
lean_ctor_set(v___x_4060_, 2, v___x_4063_);
v___x_4065_ = v___x_4060_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_key_4056_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v_value_4057_);
lean_ctor_set(v_reuseFailAlloc_4066_, 2, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
else
{
lean_del_object(v___x_4060_);
lean_dec(v_value_4057_);
lean_dec(v_key_4056_);
return v_tail_4058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_4068_, lean_object* v_x_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4068_, v_x_4069_);
lean_dec(v_a_4068_);
return v_res_4070_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4071_; uint64_t v___x_4072_; 
v___x_4071_ = lean_unsigned_to_nat(1723u);
v___x_4072_ = lean_uint64_of_nat(v___x_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v_size_4075_; lean_object* v_buckets_4076_; lean_object* v___x_4077_; uint64_t v___y_4079_; 
v_size_4075_ = lean_ctor_get(v_m_4073_, 0);
v_buckets_4076_ = lean_ctor_get(v_m_4073_, 1);
v___x_4077_ = lean_array_get_size(v_buckets_4076_);
if (lean_obj_tag(v_a_4074_) == 0)
{
uint64_t v___x_4108_; 
v___x_4108_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_4079_ = v___x_4108_;
goto v___jp_4078_;
}
else
{
uint64_t v_hash_4109_; 
v_hash_4109_ = lean_ctor_get_uint64(v_a_4074_, sizeof(void*)*2);
v___y_4079_ = v_hash_4109_;
goto v___jp_4078_;
}
v___jp_4078_:
{
uint64_t v___x_4080_; uint64_t v___x_4081_; uint64_t v_fold_4082_; uint64_t v___x_4083_; uint64_t v___x_4084_; uint64_t v___x_4085_; size_t v___x_4086_; size_t v___x_4087_; size_t v___x_4088_; size_t v___x_4089_; size_t v___x_4090_; lean_object* v_bkt_4091_; uint8_t v___x_4092_; 
v___x_4080_ = 32ULL;
v___x_4081_ = lean_uint64_shift_right(v___y_4079_, v___x_4080_);
v_fold_4082_ = lean_uint64_xor(v___y_4079_, v___x_4081_);
v___x_4083_ = 16ULL;
v___x_4084_ = lean_uint64_shift_right(v_fold_4082_, v___x_4083_);
v___x_4085_ = lean_uint64_xor(v_fold_4082_, v___x_4084_);
v___x_4086_ = lean_uint64_to_usize(v___x_4085_);
v___x_4087_ = lean_usize_of_nat(v___x_4077_);
v___x_4088_ = ((size_t)1ULL);
v___x_4089_ = lean_usize_sub(v___x_4087_, v___x_4088_);
v___x_4090_ = lean_usize_land(v___x_4086_, v___x_4089_);
v_bkt_4091_ = lean_array_uget_borrowed(v_buckets_4076_, v___x_4090_);
v___x_4092_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4074_, v_bkt_4091_);
if (v___x_4092_ == 0)
{
return v_m_4073_;
}
else
{
lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4105_; 
lean_inc(v_bkt_4091_);
lean_inc_ref(v_buckets_4076_);
lean_inc(v_size_4075_);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_m_4073_);
if (v_isSharedCheck_4105_ == 0)
{
lean_object* v_unused_4106_; lean_object* v_unused_4107_; 
v_unused_4106_ = lean_ctor_get(v_m_4073_, 1);
lean_dec(v_unused_4106_);
v_unused_4107_ = lean_ctor_get(v_m_4073_, 0);
lean_dec(v_unused_4107_);
v___x_4094_ = v_m_4073_;
v_isShared_4095_ = v_isSharedCheck_4105_;
goto v_resetjp_4093_;
}
else
{
lean_dec(v_m_4073_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4105_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4096_; lean_object* v_buckets_x27_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4103_; 
v___x_4096_ = lean_box(0);
v_buckets_x27_4097_ = lean_array_uset(v_buckets_4076_, v___x_4090_, v___x_4096_);
v___x_4098_ = lean_unsigned_to_nat(1u);
v___x_4099_ = lean_nat_sub(v_size_4075_, v___x_4098_);
lean_dec(v_size_4075_);
v___x_4100_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4074_, v_bkt_4091_);
v___x_4101_ = lean_array_uset(v_buckets_x27_4097_, v___x_4090_, v___x_4100_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 1, v___x_4101_);
lean_ctor_set(v___x_4094_, 0, v___x_4099_);
v___x_4103_ = v___x_4094_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___x_4099_);
lean_ctor_set(v_reuseFailAlloc_4104_, 1, v___x_4101_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4110_, v_a_4111_);
lean_dec(v_a_4111_);
return v_res_4112_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4113_, lean_object* v_a_4114_){
_start:
{
lean_object* v_buckets_4115_; lean_object* v___x_4116_; uint64_t v___y_4118_; 
v_buckets_4115_ = lean_ctor_get(v_m_4113_, 1);
v___x_4116_ = lean_array_get_size(v_buckets_4115_);
if (lean_obj_tag(v_a_4114_) == 0)
{
uint64_t v___x_4132_; 
v___x_4132_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___closed__0);
v___y_4118_ = v___x_4132_;
goto v___jp_4117_;
}
else
{
uint64_t v_hash_4133_; 
v_hash_4133_ = lean_ctor_get_uint64(v_a_4114_, sizeof(void*)*2);
v___y_4118_ = v_hash_4133_;
goto v___jp_4117_;
}
v___jp_4117_:
{
uint64_t v___x_4119_; uint64_t v___x_4120_; uint64_t v_fold_4121_; uint64_t v___x_4122_; uint64_t v___x_4123_; uint64_t v___x_4124_; size_t v___x_4125_; size_t v___x_4126_; size_t v___x_4127_; size_t v___x_4128_; size_t v___x_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; 
v___x_4119_ = 32ULL;
v___x_4120_ = lean_uint64_shift_right(v___y_4118_, v___x_4119_);
v_fold_4121_ = lean_uint64_xor(v___y_4118_, v___x_4120_);
v___x_4122_ = 16ULL;
v___x_4123_ = lean_uint64_shift_right(v_fold_4121_, v___x_4122_);
v___x_4124_ = lean_uint64_xor(v_fold_4121_, v___x_4123_);
v___x_4125_ = lean_uint64_to_usize(v___x_4124_);
v___x_4126_ = lean_usize_of_nat(v___x_4116_);
v___x_4127_ = ((size_t)1ULL);
v___x_4128_ = lean_usize_sub(v___x_4126_, v___x_4127_);
v___x_4129_ = lean_usize_land(v___x_4125_, v___x_4128_);
v___x_4130_ = lean_array_uget_borrowed(v_buckets_4115_, v___x_4129_);
v___x_4131_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4114_, v___x_4130_);
return v___x_4131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4134_, lean_object* v_a_4135_){
_start:
{
uint8_t v_res_4136_; lean_object* v_r_4137_; 
v_res_4136_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4134_, v_a_4135_);
lean_dec(v_a_4135_);
lean_dec_ref(v_m_4134_);
v_r_4137_ = lean_box(v_res_4136_);
return v_r_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4138_, lean_object* v_as_4139_, size_t v_i_4140_, size_t v_stop_4141_, lean_object* v_b_4142_){
_start:
{
uint8_t v___x_4143_; 
v___x_4143_ = lean_usize_dec_eq(v_i_4140_, v_stop_4141_);
if (v___x_4143_ == 0)
{
size_t v___x_4144_; size_t v___x_4145_; lean_object* v___x_4146_; 
v___x_4144_ = ((size_t)1ULL);
v___x_4145_ = lean_usize_sub(v_i_4140_, v___x_4144_);
v___x_4146_ = lean_array_uget(v_as_4139_, v___x_4145_);
if (lean_obj_tag(v___x_4146_) == 0)
{
v_i_4140_ = v___x_4145_;
goto _start;
}
else
{
lean_object* v_val_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4182_; 
v_val_4148_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4150_ = v___x_4146_;
v_isShared_4151_ = v_isSharedCheck_4182_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_val_4148_);
lean_dec(v___x_4146_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4182_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v_fst_4152_; lean_object* v_snd_4153_; lean_object* v___y_4155_; lean_object* v___y_4171_; lean_object* v_size_4177_; lean_object* v___x_4178_; uint8_t v___x_4179_; 
v_fst_4152_ = lean_ctor_get(v_b_4142_, 0);
v_snd_4153_ = lean_ctor_get(v_b_4142_, 1);
v_size_4177_ = lean_ctor_get(v_fst_4152_, 0);
v___x_4178_ = lean_unsigned_to_nat(0u);
v___x_4179_ = lean_nat_dec_eq(v_size_4177_, v___x_4178_);
if (v___x_4179_ == 0)
{
lean_object* v_index_4180_; 
v_index_4180_ = lean_ctor_get(v_val_4148_, 0);
lean_inc(v_index_4180_);
v___y_4171_ = v_index_4180_;
goto v___jp_4170_;
}
else
{
lean_object* v___x_4181_; 
lean_inc(v_snd_4153_);
lean_del_object(v___x_4150_);
lean_dec(v_val_4148_);
lean_dec_ref(v_b_4142_);
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v_snd_4153_);
return v___x_4181_;
}
v___jp_4154_:
{
uint8_t v___x_4156_; 
v___x_4156_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4152_, v___y_4155_);
if (v___x_4156_ == 0)
{
lean_dec(v___y_4155_);
lean_dec(v_val_4148_);
v_i_4140_ = v___x_4145_;
goto _start;
}
else
{
lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4167_; 
lean_inc(v_snd_4153_);
lean_inc(v_fst_4152_);
v_isSharedCheck_4167_ = !lean_is_exclusive(v_b_4142_);
if (v_isSharedCheck_4167_ == 0)
{
lean_object* v_unused_4168_; lean_object* v_unused_4169_; 
v_unused_4168_ = lean_ctor_get(v_b_4142_, 1);
lean_dec(v_unused_4168_);
v_unused_4169_ = lean_ctor_get(v_b_4142_, 0);
lean_dec(v_unused_4169_);
v___x_4159_ = v_b_4142_;
v_isShared_4160_ = v_isSharedCheck_4167_;
goto v_resetjp_4158_;
}
else
{
lean_dec(v_b_4142_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4167_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4164_; 
v___x_4161_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4152_, v___y_4155_);
lean_dec(v___y_4155_);
v___x_4162_ = lean_array_push(v_snd_4153_, v_val_4148_);
if (v_isShared_4160_ == 0)
{
lean_ctor_set(v___x_4159_, 1, v___x_4162_);
lean_ctor_set(v___x_4159_, 0, v___x_4161_);
v___x_4164_ = v___x_4159_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4161_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v___x_4162_);
v___x_4164_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
v_i_4140_ = v___x_4145_;
v_b_4142_ = v___x_4164_;
goto _start;
}
}
}
}
v___jp_4170_:
{
uint8_t v___x_4172_; 
v___x_4172_ = lean_nat_dec_lt(v___y_4171_, v_start_4138_);
lean_dec(v___y_4171_);
if (v___x_4172_ == 0)
{
lean_object* v_userName_4173_; 
lean_del_object(v___x_4150_);
v_userName_4173_ = lean_ctor_get(v_val_4148_, 2);
lean_inc(v_userName_4173_);
v___y_4155_ = v_userName_4173_;
goto v___jp_4154_;
}
else
{
lean_object* v___x_4175_; 
lean_inc(v_snd_4153_);
lean_dec(v_val_4148_);
lean_dec_ref(v_b_4142_);
if (v_isShared_4151_ == 0)
{
lean_ctor_set_tag(v___x_4150_, 0);
lean_ctor_set(v___x_4150_, 0, v_snd_4153_);
v___x_4175_ = v___x_4150_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_snd_4153_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
}
}
else
{
lean_object* v___x_4183_; 
v___x_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4183_, 0, v_b_4142_);
return v___x_4183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4184_, lean_object* v_as_4185_, lean_object* v_i_4186_, lean_object* v_stop_4187_, lean_object* v_b_4188_){
_start:
{
size_t v_i_boxed_4189_; size_t v_stop_boxed_4190_; lean_object* v_res_4191_; 
v_i_boxed_4189_ = lean_unbox_usize(v_i_4186_);
lean_dec(v_i_4186_);
v_stop_boxed_4190_ = lean_unbox_usize(v_stop_4187_);
lean_dec(v_stop_4187_);
v_res_4191_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4184_, v_as_4185_, v_i_boxed_4189_, v_stop_boxed_4190_, v_b_4188_);
lean_dec_ref(v_as_4185_);
lean_dec(v_start_4184_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4192_, lean_object* v_x_4193_, lean_object* v_x_4194_){
_start:
{
if (lean_obj_tag(v_x_4193_) == 0)
{
lean_object* v_cs_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4208_; 
v_cs_4195_ = lean_ctor_get(v_x_4193_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v_x_4193_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4197_ = v_x_4193_;
v_isShared_4198_ = v_isSharedCheck_4208_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_cs_4195_);
lean_dec(v_x_4193_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4208_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; uint8_t v___x_4201_; 
v___x_4199_ = lean_array_get_size(v_cs_4195_);
v___x_4200_ = lean_unsigned_to_nat(0u);
v___x_4201_ = lean_nat_dec_lt(v___x_4200_, v___x_4199_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4203_; 
lean_dec_ref(v_cs_4195_);
if (v_isShared_4198_ == 0)
{
lean_ctor_set_tag(v___x_4197_, 1);
lean_ctor_set(v___x_4197_, 0, v_x_4194_);
v___x_4203_ = v___x_4197_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_x_4194_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
else
{
size_t v___x_4205_; size_t v___x_4206_; lean_object* v___x_4207_; 
lean_del_object(v___x_4197_);
v___x_4205_ = lean_usize_of_nat(v___x_4199_);
v___x_4206_ = ((size_t)0ULL);
v___x_4207_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4192_, v_cs_4195_, v___x_4205_, v___x_4206_, v_x_4194_);
lean_dec_ref(v_cs_4195_);
return v___x_4207_;
}
}
}
else
{
lean_object* v_vs_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4222_; 
v_vs_4209_ = lean_ctor_get(v_x_4193_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v_x_4193_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4211_ = v_x_4193_;
v_isShared_4212_ = v_isSharedCheck_4222_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_vs_4209_);
lean_dec(v_x_4193_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4222_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; uint8_t v___x_4215_; 
v___x_4213_ = lean_array_get_size(v_vs_4209_);
v___x_4214_ = lean_unsigned_to_nat(0u);
v___x_4215_ = lean_nat_dec_lt(v___x_4214_, v___x_4213_);
if (v___x_4215_ == 0)
{
lean_object* v___x_4217_; 
lean_dec_ref(v_vs_4209_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 0, v_x_4194_);
v___x_4217_ = v___x_4211_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_x_4194_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
else
{
size_t v___x_4219_; size_t v___x_4220_; lean_object* v___x_4221_; 
lean_del_object(v___x_4211_);
v___x_4219_ = lean_usize_of_nat(v___x_4213_);
v___x_4220_ = ((size_t)0ULL);
v___x_4221_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4192_, v_vs_4209_, v___x_4219_, v___x_4220_, v_x_4194_);
lean_dec_ref(v_vs_4209_);
return v___x_4221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4223_, lean_object* v_as_4224_, size_t v_i_4225_, size_t v_stop_4226_, lean_object* v_b_4227_){
_start:
{
uint8_t v___x_4228_; 
v___x_4228_ = lean_usize_dec_eq(v_i_4225_, v_stop_4226_);
if (v___x_4228_ == 0)
{
size_t v___x_4229_; size_t v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4229_ = ((size_t)1ULL);
v___x_4230_ = lean_usize_sub(v_i_4225_, v___x_4229_);
v___x_4231_ = lean_array_uget_borrowed(v_as_4224_, v___x_4230_);
lean_inc(v___x_4231_);
v___x_4232_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4223_, v___x_4231_, v_b_4227_);
if (lean_obj_tag(v___x_4232_) == 0)
{
return v___x_4232_;
}
else
{
lean_object* v_a_4233_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref_known(v___x_4232_, 1);
v_i_4225_ = v___x_4230_;
v_b_4227_ = v_a_4233_;
goto _start;
}
}
else
{
lean_object* v___x_4235_; 
v___x_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4235_, 0, v_b_4227_);
return v___x_4235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4236_, lean_object* v_as_4237_, lean_object* v_i_4238_, lean_object* v_stop_4239_, lean_object* v_b_4240_){
_start:
{
size_t v_i_boxed_4241_; size_t v_stop_boxed_4242_; lean_object* v_res_4243_; 
v_i_boxed_4241_ = lean_unbox_usize(v_i_4238_);
lean_dec(v_i_4238_);
v_stop_boxed_4242_ = lean_unbox_usize(v_stop_4239_);
lean_dec(v_stop_4239_);
v_res_4243_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4236_, v_as_4237_, v_i_boxed_4241_, v_stop_boxed_4242_, v_b_4240_);
lean_dec_ref(v_as_4237_);
lean_dec(v_start_4236_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4244_, lean_object* v_x_4245_, lean_object* v_x_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4244_, v_x_4245_, v_x_4246_);
lean_dec(v_start_4244_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4248_, lean_object* v_t_4249_, lean_object* v_init_4250_){
_start:
{
lean_object* v_root_4251_; lean_object* v_tail_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; 
v_root_4251_ = lean_ctor_get(v_t_4249_, 0);
lean_inc_ref(v_root_4251_);
v_tail_4252_ = lean_ctor_get(v_t_4249_, 1);
lean_inc_ref(v_tail_4252_);
lean_dec_ref(v_t_4249_);
v___x_4253_ = lean_array_get_size(v_tail_4252_);
v___x_4254_ = lean_unsigned_to_nat(0u);
v___x_4255_ = lean_nat_dec_lt(v___x_4254_, v___x_4253_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4256_; 
lean_dec_ref(v_tail_4252_);
v___x_4256_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4248_, v_root_4251_, v_init_4250_);
return v___x_4256_;
}
else
{
size_t v___x_4257_; size_t v___x_4258_; lean_object* v___x_4259_; 
v___x_4257_ = lean_usize_of_nat(v___x_4253_);
v___x_4258_ = ((size_t)0ULL);
v___x_4259_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4248_, v_tail_4252_, v___x_4257_, v___x_4258_, v_init_4250_);
lean_dec_ref(v_tail_4252_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_dec_ref(v_root_4251_);
return v___x_4259_;
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4261_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v___x_4259_, 1);
v___x_4261_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4248_, v_root_4251_, v_a_4260_);
return v___x_4261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4262_, lean_object* v_t_4263_, lean_object* v_init_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4262_, v_t_4263_, v_init_4264_);
lean_dec(v_start_4262_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4266_, lean_object* v_lctx_4267_, lean_object* v_init_4268_){
_start:
{
lean_object* v_decls_4269_; lean_object* v___x_4270_; 
v_decls_4269_ = lean_ctor_get(v_lctx_4267_, 1);
lean_inc_ref(v_decls_4269_);
lean_dec_ref(v_lctx_4267_);
v___x_4270_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4266_, v_decls_4269_, v_init_4268_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4271_, lean_object* v_lctx_4272_, lean_object* v_init_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4271_, v_lctx_4272_, v_init_4273_);
lean_dec(v_start_4271_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4277_, lean_object* v_userNames_4278_, lean_object* v_start_4279_){
_start:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4280_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4281_, 0, v_userNames_4278_);
lean_ctor_set(v___x_4281_, 1, v___x_4280_);
v___x_4282_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4279_, v_lctx_4277_, v___x_4281_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4284_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v___x_4284_ = l_Array_reverse___redArg(v_a_4283_);
return v___x_4284_;
}
else
{
lean_object* v_a_4285_; lean_object* v_snd_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v_a_4285_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4285_);
lean_dec_ref_known(v___x_4282_, 1);
v_snd_4286_ = lean_ctor_get(v_a_4285_, 1);
lean_inc(v_snd_4286_);
lean_dec(v_a_4285_);
v___x_4287_ = l_Array_reverse___redArg(v_snd_4286_);
v___x_4288_ = l_Array_reverse___redArg(v___x_4287_);
return v___x_4288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4289_, lean_object* v_userNames_4290_, lean_object* v_start_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4289_, v_userNames_4290_, v_start_4291_);
lean_dec(v_start_4291_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4293_, lean_object* v_lctx_4294_, lean_object* v_userNames_4295_, lean_object* v_start_4296_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4294_, v_userNames_4295_, v_start_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4298_, lean_object* v_lctx_4299_, lean_object* v_userNames_4300_, lean_object* v_start_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4298_, v_lctx_4299_, v_userNames_4300_, v_start_4301_);
lean_dec(v_start_4301_);
return v_res_4302_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4303_, lean_object* v_m_4304_, lean_object* v_a_4305_){
_start:
{
uint8_t v___x_4306_; 
v___x_4306_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4304_, v_a_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4307_, lean_object* v_m_4308_, lean_object* v_a_4309_){
_start:
{
uint8_t v_res_4310_; lean_object* v_r_4311_; 
v_res_4310_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4307_, v_m_4308_, v_a_4309_);
lean_dec(v_a_4309_);
lean_dec_ref(v_m_4308_);
v_r_4311_ = lean_box(v_res_4310_);
return v_r_4311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4312_, lean_object* v_m_4313_, lean_object* v_a_4314_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4313_, v_a_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4316_, lean_object* v_m_4317_, lean_object* v_a_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4316_, v_m_4317_, v_a_4318_);
lean_dec(v_a_4318_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4320_, lean_object* v_start_4321_, lean_object* v_lctx_4322_, lean_object* v_init_4323_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4321_, v_lctx_4322_, v_init_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4325_, lean_object* v_start_4326_, lean_object* v_lctx_4327_, lean_object* v_init_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4325_, v_start_4326_, v_lctx_4327_, v_init_4328_);
lean_dec(v_start_4326_);
return v_res_4329_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4330_, lean_object* v_a_4331_, lean_object* v_x_4332_){
_start:
{
uint8_t v___x_4333_; 
v___x_4333_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4331_, v_x_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4334_, lean_object* v_a_4335_, lean_object* v_x_4336_){
_start:
{
uint8_t v_res_4337_; lean_object* v_r_4338_; 
v_res_4337_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4334_, v_a_4335_, v_x_4336_);
lean_dec(v_x_4336_);
lean_dec(v_a_4335_);
v_r_4338_ = lean_box(v_res_4337_);
return v_r_4338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4339_, lean_object* v_a_4340_, lean_object* v_x_4341_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4340_, v_x_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4343_, lean_object* v_a_4344_, lean_object* v_x_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4343_, v_a_4344_, v_x_4345_);
lean_dec(v_a_4344_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4347_, lean_object* v_start_4348_, lean_object* v_t_4349_, lean_object* v_init_4350_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4348_, v_t_4349_, v_init_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4352_, lean_object* v_start_4353_, lean_object* v_t_4354_, lean_object* v_init_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4352_, v_start_4353_, v_t_4354_, v_init_4355_);
lean_dec(v_start_4353_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4357_, lean_object* v_start_4358_, lean_object* v_x_4359_, lean_object* v_x_4360_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4358_, v_x_4359_, v_x_4360_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4362_, lean_object* v_start_4363_, lean_object* v_x_4364_, lean_object* v_x_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4362_, v_start_4363_, v_x_4364_, v_x_4365_);
lean_dec(v_start_4363_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4367_, lean_object* v_start_4368_, lean_object* v_as_4369_, size_t v_i_4370_, size_t v_stop_4371_, lean_object* v_b_4372_){
_start:
{
lean_object* v___x_4373_; 
v___x_4373_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4368_, v_as_4369_, v_i_4370_, v_stop_4371_, v_b_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4374_, lean_object* v_start_4375_, lean_object* v_as_4376_, lean_object* v_i_4377_, lean_object* v_stop_4378_, lean_object* v_b_4379_){
_start:
{
size_t v_i_boxed_4380_; size_t v_stop_boxed_4381_; lean_object* v_res_4382_; 
v_i_boxed_4380_ = lean_unbox_usize(v_i_4377_);
lean_dec(v_i_4377_);
v_stop_boxed_4381_ = lean_unbox_usize(v_stop_4378_);
lean_dec(v_stop_4378_);
v_res_4382_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4374_, v_start_4375_, v_as_4376_, v_i_boxed_4380_, v_stop_boxed_4381_, v_b_4379_);
lean_dec_ref(v_as_4376_);
lean_dec(v_start_4375_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4383_, lean_object* v_start_4384_, lean_object* v_as_4385_, size_t v_i_4386_, size_t v_stop_4387_, lean_object* v_b_4388_){
_start:
{
lean_object* v___x_4389_; 
v___x_4389_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4384_, v_as_4385_, v_i_4386_, v_stop_4387_, v_b_4388_);
return v___x_4389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4390_, lean_object* v_start_4391_, lean_object* v_as_4392_, lean_object* v_i_4393_, lean_object* v_stop_4394_, lean_object* v_b_4395_){
_start:
{
size_t v_i_boxed_4396_; size_t v_stop_boxed_4397_; lean_object* v_res_4398_; 
v_i_boxed_4396_ = lean_unbox_usize(v_i_4393_);
lean_dec(v_i_4393_);
v_stop_boxed_4397_ = lean_unbox_usize(v_stop_4394_);
lean_dec(v_stop_4394_);
v_res_4398_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4390_, v_start_4391_, v_as_4392_, v_i_boxed_4396_, v_stop_boxed_4397_, v_b_4395_);
lean_dec_ref(v_as_4392_);
lean_dec(v_start_4391_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4399_, lean_object* v_inst_4400_){
_start:
{
lean_object* v___x_4401_; 
v___x_4401_ = lean_apply_2(v_inst_4399_, lean_box(0), v_inst_4400_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4402_, lean_object* v_n_4403_, lean_object* v_inst_4404_, lean_object* v_inst_4405_){
_start:
{
lean_object* v___x_4406_; 
v___x_4406_ = lean_apply_2(v_inst_4404_, lean_box(0), v_inst_4405_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4407_, lean_object* v_d_x3f_4408_, lean_object* v_b_4409_){
_start:
{
if (lean_obj_tag(v_d_x3f_4408_) == 0)
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4410_, 0, v_b_4409_);
v___x_4411_ = lean_apply_2(v_toPure_4407_, lean_box(0), v___x_4410_);
return v___x_4411_;
}
else
{
lean_object* v_val_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4428_; 
v_val_4412_ = lean_ctor_get(v_d_x3f_4408_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_d_x3f_4408_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4414_ = v_d_x3f_4408_;
v_isShared_4415_ = v_isSharedCheck_4428_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_val_4412_);
lean_dec(v_d_x3f_4408_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4428_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
uint8_t v___x_4416_; uint8_t v___x_4417_; 
v___x_4416_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4412_);
v___x_4417_ = lean_bool_not(v___x_4416_);
if (v___x_4417_ == 0)
{
lean_object* v___x_4419_; 
lean_dec(v_val_4412_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 0, v_b_4409_);
v___x_4419_ = v___x_4414_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_b_4409_);
v___x_4419_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_apply_2(v_toPure_4407_, lean_box(0), v___x_4419_);
return v___x_4420_;
}
}
else
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4425_; 
v___x_4422_ = l_Lean_LocalDecl_toExpr(v_val_4412_);
v___x_4423_ = lean_array_push(v_b_4409_, v___x_4422_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 0, v___x_4423_);
v___x_4425_ = v___x_4414_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4423_);
v___x_4425_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
lean_object* v___x_4426_; 
v___x_4426_ = lean_apply_2(v_toPure_4407_, lean_box(0), v___x_4425_);
return v___x_4426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4429_, lean_object* v_____s_4430_){
_start:
{
lean_object* v___x_4431_; 
v___x_4431_ = lean_apply_2(v_toPure_4429_, lean_box(0), v_____s_4430_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4432_, lean_object* v_hs_4433_, lean_object* v___f_4434_, lean_object* v_toBind_4435_, lean_object* v___f_4436_, lean_object* v_____do__lift_4437_){
_start:
{
lean_object* v_decls_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v_decls_4438_ = lean_ctor_get(v_____do__lift_4437_, 1);
v___x_4439_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4432_, v_decls_4438_, v_hs_4433_, v___f_4434_);
v___x_4440_ = lean_apply_4(v_toBind_4435_, lean_box(0), lean_box(0), v___x_4439_, v___f_4436_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object* v_inst_4441_, lean_object* v_hs_4442_, lean_object* v___f_4443_, lean_object* v_toBind_4444_, lean_object* v___f_4445_, lean_object* v_____do__lift_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l_Lean_getLocalHyps___redArg___lam__2(v_inst_4441_, v_hs_4442_, v___f_4443_, v_toBind_4444_, v___f_4445_, v_____do__lift_4446_);
lean_dec_ref(v_____do__lift_4446_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4450_, lean_object* v_inst_4451_){
_start:
{
lean_object* v_toApplicative_4452_; lean_object* v_toBind_4453_; lean_object* v_toPure_4454_; lean_object* v_hs_4455_; lean_object* v___f_4456_; lean_object* v___f_4457_; lean_object* v___f_4458_; lean_object* v___x_4459_; 
v_toApplicative_4452_ = lean_ctor_get(v_inst_4450_, 0);
v_toBind_4453_ = lean_ctor_get(v_inst_4450_, 1);
lean_inc_n(v_toBind_4453_, 2);
v_toPure_4454_ = lean_ctor_get(v_toApplicative_4452_, 1);
v_hs_4455_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4454_, 2);
v___f_4456_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4456_, 0, v_toPure_4454_);
v___f_4457_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4457_, 0, v_toPure_4454_);
v___f_4458_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_4458_, 0, v_inst_4450_);
lean_closure_set(v___f_4458_, 1, v_hs_4455_);
lean_closure_set(v___f_4458_, 2, v___f_4456_);
lean_closure_set(v___f_4458_, 3, v_toBind_4453_);
lean_closure_set(v___f_4458_, 4, v___f_4457_);
v___x_4459_ = lean_apply_4(v_toBind_4453_, lean_box(0), lean_box(0), v_inst_4451_, v___f_4458_);
return v___x_4459_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4460_, lean_object* v_inst_4461_, lean_object* v_inst_4462_){
_start:
{
lean_object* v___x_4463_; 
v___x_4463_ = l_Lean_getLocalHyps___redArg(v_inst_4461_, v_inst_4462_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4464_, lean_object* v_e_4465_, lean_object* v_d_4466_){
_start:
{
lean_object* v___y_4468_; lean_object* v_fvarId_4500_; 
v_fvarId_4500_ = lean_ctor_get(v_d_4466_, 1);
lean_inc(v_fvarId_4500_);
v___y_4468_ = v_fvarId_4500_;
goto v___jp_4467_;
v___jp_4467_:
{
uint8_t v___x_4469_; 
v___x_4469_ = l_Lean_instBEqFVarId_beq(v___y_4468_, v_fvarId_4464_);
lean_dec(v___y_4468_);
if (v___x_4469_ == 0)
{
if (lean_obj_tag(v_d_4466_) == 0)
{
lean_object* v_index_4470_; lean_object* v_fvarId_4471_; lean_object* v_userName_4472_; lean_object* v_type_4473_; uint8_t v_bi_4474_; uint8_t v_kind_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4483_; 
v_index_4470_ = lean_ctor_get(v_d_4466_, 0);
v_fvarId_4471_ = lean_ctor_get(v_d_4466_, 1);
v_userName_4472_ = lean_ctor_get(v_d_4466_, 2);
v_type_4473_ = lean_ctor_get(v_d_4466_, 3);
v_bi_4474_ = lean_ctor_get_uint8(v_d_4466_, sizeof(void*)*4);
v_kind_4475_ = lean_ctor_get_uint8(v_d_4466_, sizeof(void*)*4 + 1);
v_isSharedCheck_4483_ = !lean_is_exclusive(v_d_4466_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4477_ = v_d_4466_;
v_isShared_4478_ = v_isSharedCheck_4483_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_type_4473_);
lean_inc(v_userName_4472_);
lean_inc(v_fvarId_4471_);
lean_inc(v_index_4470_);
lean_dec(v_d_4466_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4483_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4479_; lean_object* v___x_4481_; 
v___x_4479_ = l_Lean_Expr_replaceFVarId(v_type_4473_, v_fvarId_4464_, v_e_4465_);
lean_dec_ref(v_type_4473_);
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 3, v___x_4479_);
v___x_4481_ = v___x_4477_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_index_4470_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v_fvarId_4471_);
lean_ctor_set(v_reuseFailAlloc_4482_, 2, v_userName_4472_);
lean_ctor_set(v_reuseFailAlloc_4482_, 3, v___x_4479_);
lean_ctor_set_uint8(v_reuseFailAlloc_4482_, sizeof(void*)*4, v_bi_4474_);
lean_ctor_set_uint8(v_reuseFailAlloc_4482_, sizeof(void*)*4 + 1, v_kind_4475_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
else
{
lean_object* v_index_4484_; lean_object* v_fvarId_4485_; lean_object* v_userName_4486_; lean_object* v_type_4487_; lean_object* v_value_4488_; uint8_t v_nondep_4489_; uint8_t v_kind_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4499_; 
v_index_4484_ = lean_ctor_get(v_d_4466_, 0);
v_fvarId_4485_ = lean_ctor_get(v_d_4466_, 1);
v_userName_4486_ = lean_ctor_get(v_d_4466_, 2);
v_type_4487_ = lean_ctor_get(v_d_4466_, 3);
v_value_4488_ = lean_ctor_get(v_d_4466_, 4);
v_nondep_4489_ = lean_ctor_get_uint8(v_d_4466_, sizeof(void*)*5);
v_kind_4490_ = lean_ctor_get_uint8(v_d_4466_, sizeof(void*)*5 + 1);
v_isSharedCheck_4499_ = !lean_is_exclusive(v_d_4466_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4492_ = v_d_4466_;
v_isShared_4493_ = v_isSharedCheck_4499_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_value_4488_);
lean_inc(v_type_4487_);
lean_inc(v_userName_4486_);
lean_inc(v_fvarId_4485_);
lean_inc(v_index_4484_);
lean_dec(v_d_4466_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4499_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4497_; 
lean_inc(v_fvarId_4464_);
v___x_4494_ = l_Lean_Expr_replaceFVarId(v_type_4487_, v_fvarId_4464_, v_e_4465_);
lean_dec_ref(v_type_4487_);
v___x_4495_ = l_Lean_Expr_replaceFVarId(v_value_4488_, v_fvarId_4464_, v_e_4465_);
lean_dec_ref(v_value_4488_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 4, v___x_4495_);
lean_ctor_set(v___x_4492_, 3, v___x_4494_);
v___x_4497_ = v___x_4492_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_index_4484_);
lean_ctor_set(v_reuseFailAlloc_4498_, 1, v_fvarId_4485_);
lean_ctor_set(v_reuseFailAlloc_4498_, 2, v_userName_4486_);
lean_ctor_set(v_reuseFailAlloc_4498_, 3, v___x_4494_);
lean_ctor_set(v_reuseFailAlloc_4498_, 4, v___x_4495_);
lean_ctor_set_uint8(v_reuseFailAlloc_4498_, sizeof(void*)*5, v_nondep_4489_);
lean_ctor_set_uint8(v_reuseFailAlloc_4498_, sizeof(void*)*5 + 1, v_kind_4490_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
else
{
lean_dec(v_fvarId_4464_);
return v_d_4466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4501_, lean_object* v_e_4502_, lean_object* v_d_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4501_, v_e_4502_, v_d_4503_);
lean_dec_ref(v_e_4502_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4505_, lean_object* v_e_4506_, lean_object* v_x_4507_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4505_, v_e_4506_, v_x_4507_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4509_, lean_object* v_e_4510_, lean_object* v_x_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4509_, v_e_4510_, v_x_4511_);
lean_dec_ref(v_e_4510_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4513_, lean_object* v_e_4514_, size_t v_sz_4515_, size_t v_i_4516_, lean_object* v_bs_4517_){
_start:
{
uint8_t v___x_4518_; 
v___x_4518_ = lean_usize_dec_lt(v_i_4516_, v_sz_4515_);
if (v___x_4518_ == 0)
{
lean_dec(v_fvarId_4513_);
return v_bs_4517_;
}
else
{
lean_object* v_v_4519_; lean_object* v___x_4520_; lean_object* v_bs_x27_4521_; lean_object* v___y_4523_; 
v_v_4519_ = lean_array_uget(v_bs_4517_, v_i_4516_);
v___x_4520_ = lean_unsigned_to_nat(0u);
v_bs_x27_4521_ = lean_array_uset(v_bs_4517_, v_i_4516_, v___x_4520_);
if (lean_obj_tag(v_v_4519_) == 0)
{
v___y_4523_ = v_v_4519_;
goto v___jp_4522_;
}
else
{
lean_object* v_val_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4536_; 
v_val_4528_ = lean_ctor_get(v_v_4519_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v_v_4519_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4530_ = v_v_4519_;
v_isShared_4531_ = v_isSharedCheck_4536_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_val_4528_);
lean_dec(v_v_4519_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4536_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4532_; lean_object* v___x_4534_; 
lean_inc(v_fvarId_4513_);
v___x_4532_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4513_, v_e_4514_, v_val_4528_);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v___x_4532_);
v___x_4534_ = v___x_4530_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4532_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
v___y_4523_ = v___x_4534_;
goto v___jp_4522_;
}
}
}
v___jp_4522_:
{
size_t v___x_4524_; size_t v___x_4525_; lean_object* v___x_4526_; 
v___x_4524_ = ((size_t)1ULL);
v___x_4525_ = lean_usize_add(v_i_4516_, v___x_4524_);
v___x_4526_ = lean_array_uset(v_bs_x27_4521_, v_i_4516_, v___y_4523_);
v_i_4516_ = v___x_4525_;
v_bs_4517_ = v___x_4526_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4537_, lean_object* v_e_4538_, lean_object* v_sz_4539_, lean_object* v_i_4540_, lean_object* v_bs_4541_){
_start:
{
size_t v_sz_boxed_4542_; size_t v_i_boxed_4543_; lean_object* v_res_4544_; 
v_sz_boxed_4542_ = lean_unbox_usize(v_sz_4539_);
lean_dec(v_sz_4539_);
v_i_boxed_4543_ = lean_unbox_usize(v_i_4540_);
lean_dec(v_i_4540_);
v_res_4544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4537_, v_e_4538_, v_sz_boxed_4542_, v_i_boxed_4543_, v_bs_4541_);
lean_dec_ref(v_e_4538_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4545_, lean_object* v_e_4546_, size_t v_sz_4547_, size_t v_i_4548_, lean_object* v_bs_4549_){
_start:
{
uint8_t v___x_4550_; 
v___x_4550_ = lean_usize_dec_lt(v_i_4548_, v_sz_4547_);
if (v___x_4550_ == 0)
{
lean_dec(v_fvarId_4545_);
return v_bs_4549_;
}
else
{
lean_object* v_v_4551_; lean_object* v___x_4552_; lean_object* v_bs_x27_4553_; lean_object* v___x_4554_; size_t v___x_4555_; size_t v___x_4556_; lean_object* v___x_4557_; 
v_v_4551_ = lean_array_uget(v_bs_4549_, v_i_4548_);
v___x_4552_ = lean_unsigned_to_nat(0u);
v_bs_x27_4553_ = lean_array_uset(v_bs_4549_, v_i_4548_, v___x_4552_);
lean_inc(v_fvarId_4545_);
v___x_4554_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4545_, v_e_4546_, v_v_4551_);
v___x_4555_ = ((size_t)1ULL);
v___x_4556_ = lean_usize_add(v_i_4548_, v___x_4555_);
v___x_4557_ = lean_array_uset(v_bs_x27_4553_, v_i_4548_, v___x_4554_);
v_i_4548_ = v___x_4556_;
v_bs_4549_ = v___x_4557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4559_, lean_object* v_e_4560_, lean_object* v_x_4561_){
_start:
{
if (lean_obj_tag(v_x_4561_) == 0)
{
lean_object* v_cs_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4572_; 
v_cs_4562_ = lean_ctor_get(v_x_4561_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v_x_4561_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4564_ = v_x_4561_;
v_isShared_4565_ = v_isSharedCheck_4572_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_cs_4562_);
lean_dec(v_x_4561_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4572_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
size_t v_sz_4566_; size_t v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4570_; 
v_sz_4566_ = lean_array_size(v_cs_4562_);
v___x_4567_ = ((size_t)0ULL);
v___x_4568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4559_, v_e_4560_, v_sz_4566_, v___x_4567_, v_cs_4562_);
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v___x_4568_);
v___x_4570_ = v___x_4564_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4568_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
else
{
lean_object* v_vs_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4583_; 
v_vs_4573_ = lean_ctor_get(v_x_4561_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v_x_4561_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4575_ = v_x_4561_;
v_isShared_4576_ = v_isSharedCheck_4583_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_vs_4573_);
lean_dec(v_x_4561_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4583_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
size_t v_sz_4577_; size_t v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4581_; 
v_sz_4577_ = lean_array_size(v_vs_4573_);
v___x_4578_ = ((size_t)0ULL);
v___x_4579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4559_, v_e_4560_, v_sz_4577_, v___x_4578_, v_vs_4573_);
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 0, v___x_4579_);
v___x_4581_ = v___x_4575_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4579_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4584_, lean_object* v_e_4585_, lean_object* v_x_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4584_, v_e_4585_, v_x_4586_);
lean_dec_ref(v_e_4585_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4588_, lean_object* v_e_4589_, lean_object* v_sz_4590_, lean_object* v_i_4591_, lean_object* v_bs_4592_){
_start:
{
size_t v_sz_boxed_4593_; size_t v_i_boxed_4594_; lean_object* v_res_4595_; 
v_sz_boxed_4593_ = lean_unbox_usize(v_sz_4590_);
lean_dec(v_sz_4590_);
v_i_boxed_4594_ = lean_unbox_usize(v_i_4591_);
lean_dec(v_i_4591_);
v_res_4595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4588_, v_e_4589_, v_sz_boxed_4593_, v_i_boxed_4594_, v_bs_4592_);
lean_dec_ref(v_e_4589_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4596_, lean_object* v_e_4597_, lean_object* v_t_4598_){
_start:
{
lean_object* v_root_4599_; lean_object* v_tail_4600_; lean_object* v_size_4601_; size_t v_shift_4602_; lean_object* v_tailOff_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4614_; 
v_root_4599_ = lean_ctor_get(v_t_4598_, 0);
v_tail_4600_ = lean_ctor_get(v_t_4598_, 1);
v_size_4601_ = lean_ctor_get(v_t_4598_, 2);
v_shift_4602_ = lean_ctor_get_usize(v_t_4598_, 4);
v_tailOff_4603_ = lean_ctor_get(v_t_4598_, 3);
v_isSharedCheck_4614_ = !lean_is_exclusive(v_t_4598_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4605_ = v_t_4598_;
v_isShared_4606_ = v_isSharedCheck_4614_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_tailOff_4603_);
lean_inc(v_size_4601_);
lean_inc(v_tail_4600_);
lean_inc(v_root_4599_);
lean_dec(v_t_4598_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4614_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4607_; size_t v_sz_4608_; size_t v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4612_; 
lean_inc(v_fvarId_4596_);
v___x_4607_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4596_, v_e_4597_, v_root_4599_);
v_sz_4608_ = lean_array_size(v_tail_4600_);
v___x_4609_ = ((size_t)0ULL);
v___x_4610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4596_, v_e_4597_, v_sz_4608_, v___x_4609_, v_tail_4600_);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 1, v___x_4610_);
lean_ctor_set(v___x_4605_, 0, v___x_4607_);
v___x_4612_ = v___x_4605_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4607_);
lean_ctor_set(v_reuseFailAlloc_4613_, 1, v___x_4610_);
lean_ctor_set(v_reuseFailAlloc_4613_, 2, v_size_4601_);
lean_ctor_set(v_reuseFailAlloc_4613_, 3, v_tailOff_4603_);
lean_ctor_set_usize(v_reuseFailAlloc_4613_, 4, v_shift_4602_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4615_, lean_object* v_e_4616_, lean_object* v_t_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4615_, v_e_4616_, v_t_4617_);
lean_dec_ref(v_e_4616_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4619_, lean_object* v_x_4620_){
_start:
{
lean_object* v___x_4621_; 
v___x_4621_ = lean_apply_1(v_f_4619_, v_x_4620_);
return v___x_4621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4622_, lean_object* v_as_4623_, lean_object* v_i_4624_, lean_object* v_acc_4625_){
_start:
{
lean_object* v___x_4626_; uint8_t v___x_4627_; 
v___x_4626_ = lean_array_get_size(v_as_4623_);
v___x_4627_ = lean_nat_dec_eq(v_i_4624_, v___x_4626_);
if (v___x_4627_ == 0)
{
lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4628_ = lean_array_fget_borrowed(v_as_4623_, v_i_4624_);
lean_inc(v_f_4622_);
lean_inc(v___x_4628_);
v___x_4629_ = lean_apply_1(v_f_4622_, v___x_4628_);
v___x_4630_ = lean_unsigned_to_nat(1u);
v___x_4631_ = lean_nat_add(v_i_4624_, v___x_4630_);
lean_dec(v_i_4624_);
v___x_4632_ = lean_array_push(v_acc_4625_, v___x_4629_);
v_i_4624_ = v___x_4631_;
v_acc_4625_ = v___x_4632_;
goto _start;
}
else
{
lean_dec(v_i_4624_);
lean_dec(v_f_4622_);
return v_acc_4625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4634_, lean_object* v_as_4635_, lean_object* v_i_4636_, lean_object* v_acc_4637_){
_start:
{
lean_object* v_res_4638_; 
v_res_4638_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4634_, v_as_4635_, v_i_4636_, v_acc_4637_);
lean_dec_ref(v_as_4635_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4639_, lean_object* v_as_4640_){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4641_ = lean_unsigned_to_nat(0u);
v___x_4642_ = lean_array_get_size(v_as_4640_);
v___x_4643_ = lean_mk_empty_array_with_capacity(v___x_4642_);
v___x_4644_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4639_, v_as_4640_, v___x_4641_, v___x_4643_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4645_, lean_object* v_as_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4645_, v_as_4646_);
lean_dec_ref(v_as_4646_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4648_, size_t v_sz_4649_, size_t v_i_4650_, lean_object* v_bs_4651_){
_start:
{
uint8_t v___x_4652_; 
v___x_4652_ = lean_usize_dec_lt(v_i_4650_, v_sz_4649_);
if (v___x_4652_ == 0)
{
lean_dec(v_f_4648_);
return v_bs_4651_;
}
else
{
lean_object* v_v_4653_; lean_object* v___x_4654_; lean_object* v_bs_x27_4655_; lean_object* v___y_4657_; 
v_v_4653_ = lean_array_uget(v_bs_4651_, v_i_4650_);
v___x_4654_ = lean_unsigned_to_nat(0u);
v_bs_x27_4655_ = lean_array_uset(v_bs_4651_, v_i_4650_, v___x_4654_);
switch(lean_obj_tag(v_v_4653_))
{
case 0:
{
lean_object* v_key_4662_; lean_object* v_val_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4671_; 
v_key_4662_ = lean_ctor_get(v_v_4653_, 0);
v_val_4663_ = lean_ctor_get(v_v_4653_, 1);
v_isSharedCheck_4671_ = !lean_is_exclusive(v_v_4653_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4665_ = v_v_4653_;
v_isShared_4666_ = v_isSharedCheck_4671_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_val_4663_);
lean_inc(v_key_4662_);
lean_dec(v_v_4653_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4671_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4667_; lean_object* v___x_4669_; 
lean_inc(v_f_4648_);
v___x_4667_ = lean_apply_1(v_f_4648_, v_val_4663_);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 1, v___x_4667_);
v___x_4669_ = v___x_4665_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_key_4662_);
lean_ctor_set(v_reuseFailAlloc_4670_, 1, v___x_4667_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
v___y_4657_ = v___x_4669_;
goto v___jp_4656_;
}
}
}
case 1:
{
lean_object* v_node_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4680_; 
v_node_4672_ = lean_ctor_get(v_v_4653_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v_v_4653_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4674_ = v_v_4653_;
v_isShared_4675_ = v_isSharedCheck_4680_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_node_4672_);
lean_dec(v_v_4653_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4680_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4676_; lean_object* v___x_4678_; 
lean_inc(v_f_4648_);
v___x_4676_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4648_, v_node_4672_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set(v___x_4674_, 0, v___x_4676_);
v___x_4678_ = v___x_4674_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
v___y_4657_ = v___x_4678_;
goto v___jp_4656_;
}
}
}
default: 
{
lean_object* v___x_4681_; 
v___x_4681_ = lean_box(2);
v___y_4657_ = v___x_4681_;
goto v___jp_4656_;
}
}
v___jp_4656_:
{
size_t v___x_4658_; size_t v___x_4659_; lean_object* v___x_4660_; 
v___x_4658_ = ((size_t)1ULL);
v___x_4659_ = lean_usize_add(v_i_4650_, v___x_4658_);
v___x_4660_ = lean_array_uset(v_bs_x27_4655_, v_i_4650_, v___y_4657_);
v_i_4650_ = v___x_4659_;
v_bs_4651_ = v___x_4660_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4682_, lean_object* v_n_4683_){
_start:
{
if (lean_obj_tag(v_n_4683_) == 0)
{
lean_object* v_es_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4694_; 
v_es_4684_ = lean_ctor_get(v_n_4683_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v_n_4683_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4686_ = v_n_4683_;
v_isShared_4687_ = v_isSharedCheck_4694_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_es_4684_);
lean_dec(v_n_4683_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4694_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
size_t v_sz_4688_; size_t v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4692_; 
v_sz_4688_ = lean_array_size(v_es_4684_);
v___x_4689_ = ((size_t)0ULL);
v___x_4690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4682_, v_sz_4688_, v___x_4689_, v_es_4684_);
if (v_isShared_4687_ == 0)
{
lean_ctor_set(v___x_4686_, 0, v___x_4690_);
v___x_4692_ = v___x_4686_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4690_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
else
{
lean_object* v_ks_4695_; lean_object* v_vs_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4704_; 
v_ks_4695_ = lean_ctor_get(v_n_4683_, 0);
v_vs_4696_ = lean_ctor_get(v_n_4683_, 1);
v_isSharedCheck_4704_ = !lean_is_exclusive(v_n_4683_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4698_ = v_n_4683_;
v_isShared_4699_ = v_isSharedCheck_4704_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_vs_4696_);
lean_inc(v_ks_4695_);
lean_dec(v_n_4683_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4704_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v_val_4700_; lean_object* v___x_4702_; 
v_val_4700_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4682_, v_vs_4696_);
lean_dec_ref(v_vs_4696_);
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 1, v_val_4700_);
v___x_4702_ = v___x_4698_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_ks_4695_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v_val_4700_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4705_, lean_object* v_sz_4706_, lean_object* v_i_4707_, lean_object* v_bs_4708_){
_start:
{
size_t v_sz_boxed_4709_; size_t v_i_boxed_4710_; lean_object* v_res_4711_; 
v_sz_boxed_4709_ = lean_unbox_usize(v_sz_4706_);
lean_dec(v_sz_4706_);
v_i_boxed_4710_ = lean_unbox_usize(v_i_4707_);
lean_dec(v_i_4707_);
v_res_4711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4705_, v_sz_boxed_4709_, v_i_boxed_4710_, v_bs_4708_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4712_, lean_object* v_f_4713_){
_start:
{
lean_object* v___f_4714_; lean_object* v___x_4715_; 
v___f_4714_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4714_, 0, v_f_4713_);
v___x_4715_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4714_, v_pm_4712_);
return v___x_4715_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4716_, lean_object* v_e_4717_, lean_object* v_lctx_4718_){
_start:
{
lean_object* v_lctx_4719_; lean_object* v_fvarIdToDecl_4720_; lean_object* v_decls_4721_; lean_object* v_auxDeclToFullName_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4732_; 
lean_inc(v_fvarId_4716_);
v_lctx_4719_ = lean_local_ctx_erase(v_lctx_4718_, v_fvarId_4716_);
v_fvarIdToDecl_4720_ = lean_ctor_get(v_lctx_4719_, 0);
v_decls_4721_ = lean_ctor_get(v_lctx_4719_, 1);
v_auxDeclToFullName_4722_ = lean_ctor_get(v_lctx_4719_, 2);
v_isSharedCheck_4732_ = !lean_is_exclusive(v_lctx_4719_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4724_ = v_lctx_4719_;
v_isShared_4725_ = v_isSharedCheck_4732_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_auxDeclToFullName_4722_);
lean_inc(v_decls_4721_);
lean_inc(v_fvarIdToDecl_4720_);
lean_dec(v_lctx_4719_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4732_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___f_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4730_; 
lean_inc_ref(v_e_4717_);
lean_inc(v_fvarId_4716_);
v___f_4726_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4726_, 0, v_fvarId_4716_);
lean_closure_set(v___f_4726_, 1, v_e_4717_);
v___x_4727_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4720_, v___f_4726_);
v___x_4728_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4716_, v_e_4717_, v_decls_4721_);
lean_dec_ref(v_e_4717_);
if (v_isShared_4725_ == 0)
{
lean_ctor_set(v___x_4724_, 1, v___x_4728_);
lean_ctor_set(v___x_4724_, 0, v___x_4727_);
v___x_4730_ = v___x_4724_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4727_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v___x_4728_);
lean_ctor_set(v_reuseFailAlloc_4731_, 2, v_auxDeclToFullName_4722_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4733_, lean_object* v_00_u03c3_4734_, lean_object* v_pm_4735_, lean_object* v_f_4736_){
_start:
{
lean_object* v___x_4737_; 
v___x_4737_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4735_, v_f_4736_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4738_, lean_object* v_f_4739_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4739_, v_pm_4738_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4741_, lean_object* v_00_u03c3_4742_, lean_object* v_pm_4743_, lean_object* v_f_4744_){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4744_, v_pm_4743_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4746_, lean_object* v_00_u03b2_4747_, lean_object* v_00_u03c3_4748_, lean_object* v_f_4749_, lean_object* v_n_4750_){
_start:
{
lean_object* v___x_4751_; 
v___x_4751_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4749_, v_n_4750_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4752_, lean_object* v_00_u03b2_4753_, lean_object* v_00_u03c3_4754_, lean_object* v_f_4755_, size_t v_sz_4756_, size_t v_i_4757_, lean_object* v_bs_4758_){
_start:
{
lean_object* v___x_4759_; 
v___x_4759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4755_, v_sz_4756_, v_i_4757_, v_bs_4758_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4760_, lean_object* v_00_u03b2_4761_, lean_object* v_00_u03c3_4762_, lean_object* v_f_4763_, lean_object* v_sz_4764_, lean_object* v_i_4765_, lean_object* v_bs_4766_){
_start:
{
size_t v_sz_boxed_4767_; size_t v_i_boxed_4768_; lean_object* v_res_4769_; 
v_sz_boxed_4767_ = lean_unbox_usize(v_sz_4764_);
lean_dec(v_sz_4764_);
v_i_boxed_4768_ = lean_unbox_usize(v_i_4765_);
lean_dec(v_i_4765_);
v_res_4769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4760_, v_00_u03b2_4761_, v_00_u03c3_4762_, v_f_4763_, v_sz_boxed_4767_, v_i_boxed_4768_, v_bs_4766_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4770_, lean_object* v_00_u03b2_4771_, lean_object* v_f_4772_, lean_object* v_as_4773_){
_start:
{
lean_object* v___x_4774_; 
v___x_4774_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4772_, v_as_4773_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4775_, lean_object* v_00_u03b2_4776_, lean_object* v_f_4777_, lean_object* v_as_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4775_, v_00_u03b2_4776_, v_f_4777_, v_as_4778_);
lean_dec_ref(v_as_4778_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4780_, lean_object* v_00_u03b2_4781_, lean_object* v_f_4782_, lean_object* v_as_4783_, lean_object* v_i_4784_, lean_object* v_acc_4785_, lean_object* v_hle_4786_){
_start:
{
lean_object* v___x_4787_; 
v___x_4787_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4782_, v_as_4783_, v_i_4784_, v_acc_4785_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4788_, lean_object* v_00_u03b2_4789_, lean_object* v_f_4790_, lean_object* v_as_4791_, lean_object* v_i_4792_, lean_object* v_acc_4793_, lean_object* v_hle_4794_){
_start:
{
lean_object* v_res_4795_; 
v_res_4795_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4788_, v_00_u03b2_4789_, v_f_4790_, v_as_4791_, v_i_4792_, v_acc_4793_, v_hle_4794_);
lean_dec_ref(v_as_4791_);
return v_res_4795_;
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
