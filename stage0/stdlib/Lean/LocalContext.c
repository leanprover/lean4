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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
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
static lean_once_cell_t l_Lean_LocalDecl_isAuxDecl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_isAuxDecl___closed__0;
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object*);
static lean_once_cell_t l_Lean_LocalDecl_isImplementationDetail___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_isImplementationDetail___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_LocalDeclKind_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_LocalDeclKind_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg(lean_object* v_default_23_){
_start:
{
lean_inc(v_default_23_);
return v_default_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___redArg___boxed(lean_object* v_default_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_LocalDeclKind_default_elim___redArg(v_default_24_);
lean_dec(v_default_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_default_29_){
_start:
{
lean_inc(v_default_29_);
return v_default_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_default_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_default_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_LocalDeclKind_default_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_default_33_);
lean_dec(v_default_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg(lean_object* v_implDetail_36_){
_start:
{
lean_inc(v_implDetail_36_);
return v_implDetail_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___redArg___boxed(lean_object* v_implDetail_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_LocalDeclKind_implDetail_elim___redArg(v_implDetail_37_);
lean_dec(v_implDetail_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_implDetail_42_){
_start:
{
lean_inc(v_implDetail_42_);
return v_implDetail_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_implDetail_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_implDetail_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_LocalDeclKind_implDetail_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_implDetail_46_);
lean_dec(v_implDetail_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg(lean_object* v_auxDecl_49_){
_start:
{
lean_inc(v_auxDecl_49_);
return v_auxDecl_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___redArg___boxed(lean_object* v_auxDecl_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_LocalDeclKind_auxDecl_elim___redArg(v_auxDecl_50_);
lean_dec(v_auxDecl_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_auxDecl_55_){
_start:
{
lean_inc(v_auxDecl_55_);
return v_auxDecl_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_auxDecl_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_auxDecl_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_LocalDeclKind_auxDecl_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_auxDecl_59_);
lean_dec(v_auxDecl_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_instInhabitedLocalDeclKind(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__6(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_instReprLocalDeclKind_repr___closed__7(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr(uint8_t v_x_77_, lean_object* v_prec_78_){
_start:
{
lean_object* v___y_80_; lean_object* v___y_87_; lean_object* v___y_94_; 
switch(v_x_77_)
{
case 0:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(1024u);
v___x_101_ = lean_nat_dec_le(v___x_100_, v_prec_78_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_80_ = v___x_102_;
goto v___jp_79_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_80_ = v___x_103_;
goto v___jp_79_;
}
}
case 1:
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(1024u);
v___x_105_ = lean_nat_dec_le(v___x_104_, v_prec_78_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_87_ = v___x_106_;
goto v___jp_86_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_87_ = v___x_107_;
goto v___jp_86_;
}
}
default: 
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1024u);
v___x_109_ = lean_nat_dec_le(v___x_108_, v_prec_78_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__6, &l_Lean_instReprLocalDeclKind_repr___closed__6_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__6);
v___y_94_ = v___x_110_;
goto v___jp_93_;
}
else
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_instReprLocalDeclKind_repr___closed__7, &l_Lean_instReprLocalDeclKind_repr___closed__7_once, _init_l_Lean_instReprLocalDeclKind_repr___closed__7);
v___y_94_ = v___x_111_;
goto v___jp_93_;
}
}
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_81_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__1));
lean_inc(v___y_80_);
v___x_82_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_82_, 0, v___y_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = 0;
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_83_);
v___x_85_ = l_Repr_addAppParen(v___x_84_, v_prec_78_);
return v___x_85_;
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__3));
lean_inc(v___y_87_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_78_);
return v___x_92_;
}
v___jp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_95_ = ((lean_object*)(l_Lean_instReprLocalDeclKind_repr___closed__5));
lean_inc(v___y_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___y_94_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = 0;
v___x_98_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1, v___x_97_);
v___x_99_ = l_Repr_addAppParen(v___x_98_, v_prec_78_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprLocalDeclKind_repr___boxed(lean_object* v_x_112_, lean_object* v_prec_113_){
_start:
{
uint8_t v_x_171__boxed_114_; lean_object* v_res_115_; 
v_x_171__boxed_114_ = lean_unbox(v_x_112_);
v_res_115_ = l_Lean_instReprLocalDeclKind_repr(v_x_171__boxed_114_, v_prec_113_);
lean_dec(v_prec_113_);
return v_res_115_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDeclKind_ofNat(lean_object* v_n_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_nat_dec_le(v_n_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_dec_le(v_n_118_, v___x_121_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 2;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 1;
return v___x_124_;
}
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDeclKind_ofNat___boxed(lean_object* v_n_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Lean_LocalDeclKind_ofNat(v_n_126_);
lean_dec(v_n_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqLocalDeclKind(uint8_t v_x_129_, uint8_t v_y_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = l_Lean_LocalDeclKind_ctorIdx(v_x_129_);
v___x_132_ = l_Lean_LocalDeclKind_ctorIdx(v_y_130_);
v___x_133_ = lean_nat_dec_eq(v___x_131_, v___x_132_);
lean_dec(v___x_132_);
lean_dec(v___x_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqLocalDeclKind___boxed(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v_x_20__boxed_136_; uint8_t v_y_21__boxed_137_; uint8_t v_res_138_; lean_object* v_r_139_; 
v_x_20__boxed_136_ = lean_unbox(v_x_134_);
v_y_21__boxed_137_ = lean_unbox(v_y_135_);
v_res_138_ = l_Lean_instDecidableEqLocalDeclKind(v_x_20__boxed_136_, v_y_21__boxed_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint64_t l_Lean_instHashableLocalDeclKind_hash(uint8_t v_x_140_){
_start:
{
switch(v_x_140_)
{
case 0:
{
uint64_t v___x_141_; 
v___x_141_ = 0ULL;
return v___x_141_;
}
case 1:
{
uint64_t v___x_142_; 
v___x_142_ = 1ULL;
return v___x_142_;
}
default: 
{
uint64_t v___x_143_; 
v___x_143_ = 2ULL;
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instHashableLocalDeclKind_hash___boxed(lean_object* v_x_144_){
_start:
{
uint8_t v_x_40__boxed_145_; uint64_t v_res_146_; lean_object* v_r_147_; 
v_x_40__boxed_145_ = lean_unbox(v_x_144_);
v_res_146_ = l_Lean_instHashableLocalDeclKind_hash(v_x_40__boxed_145_);
v_r_147_ = lean_box_uint64(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx(lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v___x_151_; 
v___x_151_ = lean_unsigned_to_nat(0u);
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_unsigned_to_nat(1u);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorIdx___boxed(lean_object* v_x_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_LocalDecl_ctorIdx(v_x_153_);
lean_dec_ref(v_x_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___redArg(lean_object* v_t_155_, lean_object* v_k_156_){
_start:
{
if (lean_obj_tag(v_t_155_) == 0)
{
lean_object* v_index_157_; lean_object* v_fvarId_158_; lean_object* v_userName_159_; lean_object* v_type_160_; uint8_t v_bi_161_; uint8_t v_kind_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_index_157_ = lean_ctor_get(v_t_155_, 0);
lean_inc(v_index_157_);
v_fvarId_158_ = lean_ctor_get(v_t_155_, 1);
lean_inc(v_fvarId_158_);
v_userName_159_ = lean_ctor_get(v_t_155_, 2);
lean_inc(v_userName_159_);
v_type_160_ = lean_ctor_get(v_t_155_, 3);
lean_inc_ref(v_type_160_);
v_bi_161_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*4);
v_kind_162_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*4 + 1);
lean_dec_ref_known(v_t_155_, 4);
v___x_163_ = lean_box(v_bi_161_);
v___x_164_ = lean_box(v_kind_162_);
v___x_165_ = lean_apply_6(v_k_156_, v_index_157_, v_fvarId_158_, v_userName_159_, v_type_160_, v___x_163_, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v_index_166_; lean_object* v_fvarId_167_; lean_object* v_userName_168_; lean_object* v_type_169_; lean_object* v_value_170_; uint8_t v_nondep_171_; uint8_t v_kind_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_index_166_ = lean_ctor_get(v_t_155_, 0);
lean_inc(v_index_166_);
v_fvarId_167_ = lean_ctor_get(v_t_155_, 1);
lean_inc(v_fvarId_167_);
v_userName_168_ = lean_ctor_get(v_t_155_, 2);
lean_inc(v_userName_168_);
v_type_169_ = lean_ctor_get(v_t_155_, 3);
lean_inc_ref(v_type_169_);
v_value_170_ = lean_ctor_get(v_t_155_, 4);
lean_inc_ref(v_value_170_);
v_nondep_171_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*5);
v_kind_172_ = lean_ctor_get_uint8(v_t_155_, sizeof(void*)*5 + 1);
lean_dec_ref_known(v_t_155_, 5);
v___x_173_ = lean_box(v_nondep_171_);
v___x_174_ = lean_box(v_kind_172_);
v___x_175_ = lean_apply_7(v_k_156_, v_index_166_, v_fvarId_167_, v_userName_168_, v_type_169_, v_value_170_, v___x_173_, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim(lean_object* v_motive_176_, lean_object* v_ctorIdx_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_k_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_178_, v_k_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ctorElim___boxed(lean_object* v_motive_182_, lean_object* v_ctorIdx_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_k_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_LocalDecl_ctorElim(v_motive_182_, v_ctorIdx_183_, v_t_184_, v_h_185_, v_k_186_);
lean_dec(v_ctorIdx_183_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim___redArg(lean_object* v_t_188_, lean_object* v_cdecl_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_188_, v_cdecl_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_cdecl_elim(lean_object* v_motive_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_cdecl_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_192_, v_cdecl_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim___redArg(lean_object* v_t_196_, lean_object* v_ldecl_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_196_, v_ldecl_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ldecl_elim(lean_object* v_motive_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_ldecl_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_LocalDecl_ctorElim___redArg(v_t_200_, v_ldecl_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__2(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_box(0);
v___x_208_ = ((lean_object*)(l_Lean_instInhabitedLocalDecl_default___closed__1));
v___x_209_ = l_Lean_Expr_const___override(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default___closed__3(void){
_start:
{
uint8_t v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_210_ = 0;
v___x_211_ = 0;
v___x_212_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__2, &l_Lean_instInhabitedLocalDecl_default___closed__2_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__2);
v___x_213_ = lean_box(0);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
lean_ctor_set(v___x_215_, 2, v___x_213_);
lean_ctor_set(v___x_215_, 3, v___x_212_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*4, v___x_211_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*4 + 1, v___x_210_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl_default(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&l_Lean_instInhabitedLocalDecl_default___closed__3, &l_Lean_instInhabitedLocalDecl_default___closed__3_once, _init_l_Lean_instInhabitedLocalDecl_default___closed__3);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalDecl(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_instInhabitedLocalDecl_default;
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lean_mk_local_decl(lean_object* v_index_218_, lean_object* v_fvarId_219_, lean_object* v_userName_220_, lean_object* v_type_221_, uint8_t v_bi_222_){
_start:
{
uint8_t v___x_223_; lean_object* v___x_224_; 
v___x_223_ = 0;
v___x_224_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_224_, 0, v_index_218_);
lean_ctor_set(v___x_224_, 1, v_fvarId_219_);
lean_ctor_set(v___x_224_, 2, v_userName_220_);
lean_ctor_set(v___x_224_, 3, v_type_221_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*4, v_bi_222_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*4 + 1, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLocalDeclEx___boxed(lean_object* v_index_225_, lean_object* v_fvarId_226_, lean_object* v_userName_227_, lean_object* v_type_228_, lean_object* v_bi_229_){
_start:
{
uint8_t v_bi_boxed_230_; lean_object* v_res_231_; 
v_bi_boxed_230_ = lean_unbox(v_bi_229_);
v_res_231_ = lean_mk_local_decl(v_index_225_, v_fvarId_226_, v_userName_227_, v_type_228_, v_bi_boxed_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* lean_mk_let_decl(lean_object* v_index_232_, lean_object* v_fvarId_233_, lean_object* v_userName_234_, lean_object* v_type_235_, lean_object* v_val_236_){
_start:
{
uint8_t v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; 
v___x_237_ = 0;
v___x_238_ = 0;
v___x_239_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v___x_239_, 0, v_index_232_);
lean_ctor_set(v___x_239_, 1, v_fvarId_233_);
lean_ctor_set(v___x_239_, 2, v_userName_234_);
lean_ctor_set(v___x_239_, 3, v_type_235_);
lean_ctor_set(v___x_239_, 4, v_val_236_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*5, v___x_237_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*5 + 1, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT uint8_t lean_local_decl_binder_info(lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
uint8_t v_bi_241_; 
v_bi_241_ = lean_ctor_get_uint8(v_x_240_, sizeof(void*)*4);
lean_dec_ref_known(v_x_240_, 4);
return v_bi_241_;
}
else
{
uint8_t v___x_242_; 
lean_dec_ref(v_x_240_);
v___x_242_ = 0;
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfoEx___boxed(lean_object* v_x_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = lean_local_decl_binder_info(v_x_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isLet(lean_object* v_x_246_, uint8_t v_x_247_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
else
{
uint8_t v_nondep_249_; 
v_nondep_249_ = lean_ctor_get_uint8(v_x_246_, sizeof(void*)*5);
if (v_nondep_249_ == 0)
{
uint8_t v___x_250_; 
v___x_250_ = 1;
return v___x_250_;
}
else
{
return v_x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isLet___boxed(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
uint8_t v_x_53__boxed_253_; uint8_t v_res_254_; lean_object* v_r_255_; 
v_x_53__boxed_253_ = lean_unbox(v_x_252_);
v_res_254_ = l_Lean_LocalDecl_isLet(v_x_251_, v_x_53__boxed_253_);
lean_dec_ref(v_x_251_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index(lean_object* v_x_256_){
_start:
{
lean_object* v_index_257_; 
v_index_257_ = lean_ctor_get(v_x_256_, 0);
lean_inc(v_index_257_);
return v_index_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_index___boxed(lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_LocalDecl_index(v_x_258_);
lean_dec_ref(v_x_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setIndex(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_object* v_fvarId_262_; lean_object* v_userName_263_; lean_object* v_type_264_; uint8_t v_bi_265_; uint8_t v_kind_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_fvarId_262_ = lean_ctor_get(v_x_260_, 1);
v_userName_263_ = lean_ctor_get(v_x_260_, 2);
v_type_264_ = lean_ctor_get(v_x_260_, 3);
v_bi_265_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*4);
v_kind_266_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*4 + 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v_x_260_, 0);
lean_dec(v_unused_274_);
v___x_268_ = v_x_260_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_type_264_);
lean_inc(v_userName_263_);
lean_inc(v_fvarId_262_);
lean_dec(v_x_260_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v_x_261_);
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_x_261_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_fvarId_262_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_userName_263_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_type_264_);
lean_ctor_set_uint8(v_reuseFailAlloc_272_, sizeof(void*)*4, v_bi_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_272_, sizeof(void*)*4 + 1, v_kind_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v_fvarId_275_; lean_object* v_userName_276_; lean_object* v_type_277_; lean_object* v_value_278_; uint8_t v_nondep_279_; uint8_t v_kind_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
v_fvarId_275_ = lean_ctor_get(v_x_260_, 1);
v_userName_276_ = lean_ctor_get(v_x_260_, 2);
v_type_277_ = lean_ctor_get(v_x_260_, 3);
v_value_278_ = lean_ctor_get(v_x_260_, 4);
v_nondep_279_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*5);
v_kind_280_ = lean_ctor_get_uint8(v_x_260_, sizeof(void*)*5 + 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v_x_260_, 0);
lean_dec(v_unused_288_);
v___x_282_ = v_x_260_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_value_278_);
lean_inc(v_type_277_);
lean_inc(v_userName_276_);
lean_inc(v_fvarId_275_);
lean_dec(v_x_260_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v_x_261_);
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_x_261_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_fvarId_275_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_userName_276_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_type_277_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_value_278_);
lean_ctor_set_uint8(v_reuseFailAlloc_286_, sizeof(void*)*5, v_nondep_279_);
lean_ctor_set_uint8(v_reuseFailAlloc_286_, sizeof(void*)*5 + 1, v_kind_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId(lean_object* v_x_289_){
_start:
{
lean_object* v_fvarId_290_; 
v_fvarId_290_ = lean_ctor_get(v_x_289_, 1);
lean_inc(v_fvarId_290_);
return v_fvarId_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_fvarId___boxed(lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_LocalDecl_fvarId(v_x_291_);
lean_dec_ref(v_x_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName(lean_object* v_x_293_){
_start:
{
lean_object* v_userName_294_; 
v_userName_294_ = lean_ctor_get(v_x_293_, 2);
lean_inc(v_userName_294_);
return v_userName_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_userName___boxed(lean_object* v_x_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_LocalDecl_userName(v_x_295_);
lean_dec_ref(v_x_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type(lean_object* v_x_297_){
_start:
{
lean_object* v_type_298_; 
v_type_298_ = lean_ctor_get(v_x_297_, 3);
lean_inc_ref(v_type_298_);
return v_type_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_type___boxed(lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_LocalDecl_type(v_x_299_);
lean_dec_ref(v_x_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setType(lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_index_303_; lean_object* v_fvarId_304_; lean_object* v_userName_305_; uint8_t v_bi_306_; uint8_t v_kind_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
v_index_303_ = lean_ctor_get(v_x_301_, 0);
v_fvarId_304_ = lean_ctor_get(v_x_301_, 1);
v_userName_305_ = lean_ctor_get(v_x_301_, 2);
v_bi_306_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*4);
v_kind_307_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*4 + 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; 
v_unused_315_ = lean_ctor_get(v_x_301_, 3);
lean_dec(v_unused_315_);
v___x_309_ = v_x_301_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_userName_305_);
lean_inc(v_fvarId_304_);
lean_inc(v_index_303_);
lean_dec(v_x_301_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 3, v_x_302_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_index_303_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_fvarId_304_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_userName_305_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_x_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*4, v_bi_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_313_, sizeof(void*)*4 + 1, v_kind_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_object* v_index_316_; lean_object* v_fvarId_317_; lean_object* v_userName_318_; lean_object* v_value_319_; uint8_t v_nondep_320_; uint8_t v_kind_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_index_316_ = lean_ctor_get(v_x_301_, 0);
v_fvarId_317_ = lean_ctor_get(v_x_301_, 1);
v_userName_318_ = lean_ctor_get(v_x_301_, 2);
v_value_319_ = lean_ctor_get(v_x_301_, 4);
v_nondep_320_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*5);
v_kind_321_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*5 + 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_x_301_, 3);
lean_dec(v_unused_329_);
v___x_323_ = v_x_301_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_value_319_);
lean_inc(v_userName_318_);
lean_inc(v_fvarId_317_);
lean_inc(v_index_316_);
lean_dec(v_x_301_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 3, v_x_302_);
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_index_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_fvarId_317_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_userName_318_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_x_302_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_value_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*5, v_nondep_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_327_, sizeof(void*)*5 + 1, v_kind_321_);
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
LEAN_EXPORT uint8_t l_Lean_LocalDecl_binderInfo(lean_object* v_x_330_){
_start:
{
if (lean_obj_tag(v_x_330_) == 0)
{
uint8_t v_bi_331_; 
v_bi_331_ = lean_ctor_get_uint8(v_x_330_, sizeof(void*)*4);
return v_bi_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_binderInfo___boxed(lean_object* v_x_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Lean_LocalDecl_binderInfo(v_x_333_);
lean_dec_ref(v_x_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_kind(lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
uint8_t v_kind_337_; 
v_kind_337_ = lean_ctor_get_uint8(v_x_336_, sizeof(void*)*4 + 1);
return v_kind_337_;
}
else
{
uint8_t v_kind_338_; 
v_kind_338_ = lean_ctor_get_uint8(v_x_336_, sizeof(void*)*5 + 1);
return v_kind_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_kind___boxed(lean_object* v_x_339_){
_start:
{
uint8_t v_res_340_; lean_object* v_r_341_; 
v_res_340_ = l_Lean_LocalDecl_kind(v_x_339_);
lean_dec_ref(v_x_339_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
static lean_object* _init_l_Lean_LocalDecl_isAuxDecl___closed__0(void){
_start:
{
uint8_t v___x_342_; lean_object* v___x_343_; 
v___x_342_ = 2;
v___x_343_ = l_Lean_LocalDeclKind_ctorIdx(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object* v_d_344_){
_start:
{
uint8_t v___y_346_; 
if (lean_obj_tag(v_d_344_) == 0)
{
uint8_t v_kind_350_; 
v_kind_350_ = lean_ctor_get_uint8(v_d_344_, sizeof(void*)*4 + 1);
v___y_346_ = v_kind_350_;
goto v___jp_345_;
}
else
{
uint8_t v_kind_351_; 
v_kind_351_ = lean_ctor_get_uint8(v_d_344_, sizeof(void*)*5 + 1);
v___y_346_ = v_kind_351_;
goto v___jp_345_;
}
v___jp_345_:
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = l_Lean_LocalDeclKind_ctorIdx(v___y_346_);
v___x_348_ = lean_obj_once(&l_Lean_LocalDecl_isAuxDecl___closed__0, &l_Lean_LocalDecl_isAuxDecl___closed__0_once, _init_l_Lean_LocalDecl_isAuxDecl___closed__0);
v___x_349_ = lean_nat_dec_eq(v___x_347_, v___x_348_);
lean_dec(v___x_347_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isAuxDecl___boxed(lean_object* v_d_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Lean_LocalDecl_isAuxDecl(v_d_352_);
lean_dec_ref(v_d_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
static lean_object* _init_l_Lean_LocalDecl_isImplementationDetail___closed__0(void){
_start:
{
uint8_t v___x_355_; lean_object* v___x_356_; 
v___x_355_ = 0;
v___x_356_ = l_Lean_LocalDeclKind_ctorIdx(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object* v_d_357_){
_start:
{
uint8_t v___y_359_; 
if (lean_obj_tag(v_d_357_) == 0)
{
uint8_t v_kind_365_; 
v_kind_365_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*4 + 1);
v___y_359_ = v_kind_365_;
goto v___jp_358_;
}
else
{
uint8_t v_kind_366_; 
v_kind_366_ = lean_ctor_get_uint8(v_d_357_, sizeof(void*)*5 + 1);
v___y_359_ = v_kind_366_;
goto v___jp_358_;
}
v___jp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = l_Lean_LocalDeclKind_ctorIdx(v___y_359_);
v___x_361_ = lean_obj_once(&l_Lean_LocalDecl_isImplementationDetail___closed__0, &l_Lean_LocalDecl_isImplementationDetail___closed__0_once, _init_l_Lean_LocalDecl_isImplementationDetail___closed__0);
v___x_362_ = lean_nat_dec_eq(v___x_360_, v___x_361_);
lean_dec(v___x_360_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; 
v___x_363_ = 1;
return v___x_363_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = 0;
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isImplementationDetail___boxed(lean_object* v_d_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Lean_LocalDecl_isImplementationDetail(v_d_367_);
lean_dec_ref(v_d_367_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f(lean_object* v_x_370_, uint8_t v_x_371_){
_start:
{
if (lean_obj_tag(v_x_370_) == 1)
{
uint8_t v_nondep_372_; 
v_nondep_372_ = lean_ctor_get_uint8(v_x_370_, sizeof(void*)*5);
if (v_nondep_372_ == 0)
{
lean_object* v_value_373_; lean_object* v___x_374_; 
v_value_373_ = lean_ctor_get(v_x_370_, 4);
lean_inc_ref(v_value_373_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v_value_373_);
return v___x_374_;
}
else
{
if (v_x_371_ == 1)
{
lean_object* v_value_375_; lean_object* v___x_376_; 
v_value_375_ = lean_ctor_get(v_x_370_, 4);
lean_inc_ref(v_value_375_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v_value_375_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_box(0);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value_x3f___boxed(lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
uint8_t v_x_47__boxed_381_; lean_object* v_res_382_; 
v_x_47__boxed_381_ = lean_unbox(v_x_380_);
v_res_382_ = l_Lean_LocalDecl_value_x3f(v_x_379_, v_x_47__boxed_381_);
lean_dec_ref(v_x_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_value_spec__0(lean_object* v_msg_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = l_Lean_instInhabitedExpr;
v___x_385_ = lean_panic_fn_borrowed(v___x_384_, v_msg_383_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__3(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_389_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__2));
v___x_390_ = lean_unsigned_to_nat(54u);
v___x_391_ = lean_unsigned_to_nat(172u);
v___x_392_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_393_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_394_ = l_mkPanicMessageWithDecl(v___x_393_, v___x_392_, v___x_391_, v___x_390_, v___x_389_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_LocalDecl_value___closed__5(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__4));
v___x_397_ = lean_unsigned_to_nat(54u);
v___x_398_ = lean_unsigned_to_nat(175u);
v___x_399_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__1));
v___x_400_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_401_ = l_mkPanicMessageWithDecl(v___x_400_, v___x_399_, v___x_398_, v___x_397_, v___x_396_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value(lean_object* v_x_402_, uint8_t v_x_403_){
_start:
{
if (lean_obj_tag(v_x_402_) == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__3, &l_Lean_LocalDecl_value___closed__3_once, _init_l_Lean_LocalDecl_value___closed__3);
v___x_405_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_404_);
return v___x_405_;
}
else
{
uint8_t v_nondep_406_; 
v_nondep_406_ = lean_ctor_get_uint8(v_x_402_, sizeof(void*)*5);
if (v_nondep_406_ == 0)
{
lean_object* v_value_407_; 
v_value_407_ = lean_ctor_get(v_x_402_, 4);
lean_inc_ref(v_value_407_);
return v_value_407_;
}
else
{
if (v_x_403_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_obj_once(&l_Lean_LocalDecl_value___closed__5, &l_Lean_LocalDecl_value___closed__5_once, _init_l_Lean_LocalDecl_value___closed__5);
v___x_409_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_408_);
return v___x_409_;
}
else
{
lean_object* v_value_410_; 
v_value_410_ = lean_ctor_get(v_x_402_, 4);
lean_inc_ref(v_value_410_);
return v_value_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_value___boxed(lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
uint8_t v_x_143__boxed_413_; lean_object* v_res_414_; 
v_x_143__boxed_413_ = lean_unbox(v_x_412_);
v_res_414_ = l_Lean_LocalDecl_value(v_x_411_, v_x_143__boxed_413_);
lean_dec_ref(v_x_411_);
return v_res_414_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasValue(lean_object* v_x_415_, uint8_t v_x_416_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
uint8_t v___x_417_; 
v___x_417_ = 0;
return v___x_417_;
}
else
{
uint8_t v_nondep_418_; 
v_nondep_418_ = lean_ctor_get_uint8(v_x_415_, sizeof(void*)*5);
if (v_nondep_418_ == 0)
{
uint8_t v___x_419_; 
v___x_419_ = 1;
return v___x_419_;
}
else
{
return v_x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasValue___boxed(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
uint8_t v_x_72__boxed_422_; uint8_t v_res_423_; lean_object* v_r_424_; 
v_x_72__boxed_422_ = lean_unbox(v_x_421_);
v_res_423_ = l_Lean_LocalDecl_hasValue(v_x_420_, v_x_72__boxed_422_);
lean_dec_ref(v_x_420_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setValue(lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
if (lean_obj_tag(v_x_425_) == 1)
{
lean_object* v_index_427_; lean_object* v_fvarId_428_; lean_object* v_userName_429_; lean_object* v_type_430_; uint8_t v_nondep_431_; uint8_t v_kind_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_index_427_ = lean_ctor_get(v_x_425_, 0);
v_fvarId_428_ = lean_ctor_get(v_x_425_, 1);
v_userName_429_ = lean_ctor_get(v_x_425_, 2);
v_type_430_ = lean_ctor_get(v_x_425_, 3);
v_nondep_431_ = lean_ctor_get_uint8(v_x_425_, sizeof(void*)*5);
v_kind_432_ = lean_ctor_get_uint8(v_x_425_, sizeof(void*)*5 + 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_x_425_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v_x_425_, 4);
lean_dec(v_unused_440_);
v___x_434_ = v_x_425_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_type_430_);
lean_inc(v_userName_429_);
lean_inc(v_fvarId_428_);
lean_inc(v_index_427_);
lean_dec(v_x_425_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 4, v_x_426_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_index_427_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_fvarId_428_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_userName_429_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_type_430_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_x_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, sizeof(void*)*5, v_nondep_431_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, sizeof(void*)*5 + 1, v_kind_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_dec_ref(v_x_426_);
return v_x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep(lean_object* v_x_441_, uint8_t v_x_442_){
_start:
{
if (lean_obj_tag(v_x_441_) == 1)
{
lean_object* v_index_443_; lean_object* v_fvarId_444_; lean_object* v_userName_445_; lean_object* v_type_446_; lean_object* v_value_447_; uint8_t v_kind_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_index_443_ = lean_ctor_get(v_x_441_, 0);
v_fvarId_444_ = lean_ctor_get(v_x_441_, 1);
v_userName_445_ = lean_ctor_get(v_x_441_, 2);
v_type_446_ = lean_ctor_get(v_x_441_, 3);
v_value_447_ = lean_ctor_get(v_x_441_, 4);
v_kind_448_ = lean_ctor_get_uint8(v_x_441_, sizeof(void*)*5 + 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v_x_441_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_value_447_);
lean_inc(v_type_446_);
lean_inc(v_userName_445_);
lean_inc(v_fvarId_444_);
lean_inc(v_index_443_);
lean_dec(v_x_441_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_index_443_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_fvarId_444_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_userName_445_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_type_446_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_value_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_454_, sizeof(void*)*5 + 1, v_kind_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*5, v_x_442_);
return v___x_453_;
}
}
}
else
{
return v_x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setNondep___boxed(lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
uint8_t v_x_23__boxed_458_; lean_object* v_res_459_; 
v_x_23__boxed_458_ = lean_unbox(v_x_457_);
v_res_459_ = l_Lean_LocalDecl_setNondep(v_x_456_, v_x_23__boxed_458_);
return v_res_459_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_isNondep(lean_object* v_x_460_){
_start:
{
if (lean_obj_tag(v_x_460_) == 1)
{
uint8_t v_nondep_461_; 
v_nondep_461_ = lean_ctor_get_uint8(v_x_460_, sizeof(void*)*5);
return v_nondep_461_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = 0;
return v___x_462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_isNondep___boxed(lean_object* v_x_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_Lean_LocalDecl_isNondep(v_x_463_);
lean_dec_ref(v_x_463_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setUserName(lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v_index_468_; lean_object* v_fvarId_469_; lean_object* v_type_470_; uint8_t v_bi_471_; uint8_t v_kind_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
v_index_468_ = lean_ctor_get(v_x_466_, 0);
v_fvarId_469_ = lean_ctor_get(v_x_466_, 1);
v_type_470_ = lean_ctor_get(v_x_466_, 3);
v_bi_471_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*4);
v_kind_472_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*4 + 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_x_466_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v_x_466_, 2);
lean_dec(v_unused_480_);
v___x_474_ = v_x_466_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_type_470_);
lean_inc(v_fvarId_469_);
lean_inc(v_index_468_);
lean_dec(v_x_466_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 2, v_x_467_);
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_index_468_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_fvarId_469_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_x_467_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_type_470_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*4, v_bi_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*4 + 1, v_kind_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_object* v_index_481_; lean_object* v_fvarId_482_; lean_object* v_type_483_; lean_object* v_value_484_; uint8_t v_nondep_485_; uint8_t v_kind_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_index_481_ = lean_ctor_get(v_x_466_, 0);
v_fvarId_482_ = lean_ctor_get(v_x_466_, 1);
v_type_483_ = lean_ctor_get(v_x_466_, 3);
v_value_484_ = lean_ctor_get(v_x_466_, 4);
v_nondep_485_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*5);
v_kind_486_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*5 + 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_x_466_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v_x_466_, 2);
lean_dec(v_unused_494_);
v___x_488_ = v_x_466_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_value_484_);
lean_inc(v_type_483_);
lean_inc(v_fvarId_482_);
lean_inc(v_index_481_);
lean_dec(v_x_466_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 2, v_x_467_);
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_index_481_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_fvarId_482_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_x_467_);
lean_ctor_set(v_reuseFailAlloc_492_, 3, v_type_483_);
lean_ctor_set(v_reuseFailAlloc_492_, 4, v_value_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_492_, sizeof(void*)*5, v_nondep_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_492_, sizeof(void*)*5 + 1, v_kind_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(lean_object* v_msg_495_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = l_Lean_instInhabitedLocalDecl_default;
v___x_497_ = lean_panic_fn_borrowed(v___x_496_, v_msg_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_LocalDecl_setBinderInfo___closed__2(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_500_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__1));
v___x_501_ = lean_unsigned_to_nat(38u);
v___x_502_ = lean_unsigned_to_nat(237u);
v___x_503_ = ((lean_object*)(l_Lean_LocalDecl_setBinderInfo___closed__0));
v___x_504_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_505_ = l_mkPanicMessageWithDecl(v___x_504_, v___x_503_, v___x_502_, v___x_501_, v___x_500_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo(lean_object* v_x_506_, uint8_t v_x_507_){
_start:
{
if (lean_obj_tag(v_x_506_) == 0)
{
lean_object* v_index_508_; lean_object* v_fvarId_509_; lean_object* v_userName_510_; lean_object* v_type_511_; uint8_t v_kind_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_index_508_ = lean_ctor_get(v_x_506_, 0);
v_fvarId_509_ = lean_ctor_get(v_x_506_, 1);
v_userName_510_ = lean_ctor_get(v_x_506_, 2);
v_type_511_ = lean_ctor_get(v_x_506_, 3);
v_kind_512_ = lean_ctor_get_uint8(v_x_506_, sizeof(void*)*4 + 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_x_506_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v_x_506_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_type_511_);
lean_inc(v_userName_510_);
lean_inc(v_fvarId_509_);
lean_inc(v_index_508_);
lean_dec(v_x_506_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_index_508_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_fvarId_509_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_userName_510_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_type_511_);
lean_ctor_set_uint8(v_reuseFailAlloc_518_, sizeof(void*)*4 + 1, v_kind_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*4, v_x_507_);
return v___x_517_;
}
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec_ref_known(v_x_506_, 5);
v___x_520_ = lean_obj_once(&l_Lean_LocalDecl_setBinderInfo___closed__2, &l_Lean_LocalDecl_setBinderInfo___closed__2_once, _init_l_Lean_LocalDecl_setBinderInfo___closed__2);
v___x_521_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_520_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setBinderInfo___boxed(lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
uint8_t v_x_84__boxed_524_; lean_object* v_res_525_; 
v_x_84__boxed_524_ = lean_unbox(v_x_523_);
v_res_525_ = l_Lean_LocalDecl_setBinderInfo(v_x_522_, v_x_84__boxed_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_toExpr(lean_object* v_decl_526_){
_start:
{
lean_object* v_fvarId_527_; lean_object* v___x_528_; 
v_fvarId_527_ = lean_ctor_get(v_decl_526_, 1);
lean_inc(v_fvarId_527_);
lean_dec_ref(v_decl_526_);
v___x_528_ = l_Lean_mkFVar(v_fvarId_527_);
return v___x_528_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalDecl_hasExprMVar(lean_object* v_x_529_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
lean_object* v_type_530_; uint8_t v___x_531_; 
v_type_530_ = lean_ctor_get(v_x_529_, 3);
v___x_531_ = l_Lean_Expr_hasExprMVar(v_type_530_);
return v___x_531_;
}
else
{
lean_object* v_type_532_; lean_object* v_value_533_; uint8_t v___x_534_; 
v_type_532_ = lean_ctor_get(v_x_529_, 3);
v_value_533_ = lean_ctor_get(v_x_529_, 4);
v___x_534_ = l_Lean_Expr_hasExprMVar(v_type_532_);
if (v___x_534_ == 0)
{
uint8_t v___x_535_; 
v___x_535_ = l_Lean_Expr_hasExprMVar(v_value_533_);
return v___x_535_;
}
else
{
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_hasExprMVar___boxed(lean_object* v_x_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_Lean_LocalDecl_hasExprMVar(v_x_536_);
lean_dec_ref(v_x_536_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind(lean_object* v_x_539_, uint8_t v_x_540_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v_index_541_; lean_object* v_fvarId_542_; lean_object* v_userName_543_; lean_object* v_type_544_; uint8_t v_bi_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_index_541_ = lean_ctor_get(v_x_539_, 0);
v_fvarId_542_ = lean_ctor_get(v_x_539_, 1);
v_userName_543_ = lean_ctor_get(v_x_539_, 2);
v_type_544_ = lean_ctor_get(v_x_539_, 3);
v_bi_545_ = lean_ctor_get_uint8(v_x_539_, sizeof(void*)*4);
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v_x_539_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_type_544_);
lean_inc(v_userName_543_);
lean_inc(v_fvarId_542_);
lean_inc(v_index_541_);
lean_dec(v_x_539_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_index_541_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_fvarId_542_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_userName_543_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_type_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_551_, sizeof(void*)*4, v_bi_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*4 + 1, v_x_540_);
return v___x_550_;
}
}
}
else
{
lean_object* v_index_553_; lean_object* v_fvarId_554_; lean_object* v_userName_555_; lean_object* v_type_556_; lean_object* v_value_557_; uint8_t v_nondep_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
v_index_553_ = lean_ctor_get(v_x_539_, 0);
v_fvarId_554_ = lean_ctor_get(v_x_539_, 1);
v_userName_555_ = lean_ctor_get(v_x_539_, 2);
v_type_556_ = lean_ctor_get(v_x_539_, 3);
v_value_557_ = lean_ctor_get(v_x_539_, 4);
v_nondep_558_ = lean_ctor_get_uint8(v_x_539_, sizeof(void*)*5);
v_isSharedCheck_565_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v_x_539_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_value_557_);
lean_inc(v_type_556_);
lean_inc(v_userName_555_);
lean_inc(v_fvarId_554_);
lean_inc(v_index_553_);
lean_dec(v_x_539_);
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
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_index_553_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_fvarId_554_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_userName_555_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_type_556_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v_value_557_);
lean_ctor_set_uint8(v_reuseFailAlloc_564_, sizeof(void*)*5, v_nondep_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*5 + 1, v_x_540_);
return v___x_563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_setKind___boxed(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
uint8_t v_x_31__boxed_568_; lean_object* v_res_569_; 
v_x_31__boxed_568_ = lean_unbox(v_x_567_);
v_res_569_ = l_Lean_LocalDecl_setKind(v_x_566_, v_x_31__boxed_568_);
return v_res_569_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__0(void){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_570_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__0, &l_Lean_instInhabitedLocalContext_default___closed__0_once, _init_l_Lean_instInhabitedLocalContext_default___closed__0);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__2(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_unsigned_to_nat(32u);
v___x_574_ = lean_mk_empty_array_with_capacity(v___x_573_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__3(void){
_start:
{
size_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_576_ = ((size_t)5ULL);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_unsigned_to_nat(32u);
v___x_579_ = lean_mk_empty_array_with_capacity(v___x_578_);
v___x_580_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__2, &l_Lean_instInhabitedLocalContext_default___closed__2_once, _init_l_Lean_instInhabitedLocalContext_default___closed__2);
v___x_581_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_577_);
lean_ctor_set(v___x_581_, 3, v___x_577_);
lean_ctor_set_usize(v___x_581_, 4, v___x_576_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default___closed__4(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_582_ = lean_box(1);
v___x_583_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__3, &l_Lean_instInhabitedLocalContext_default___closed__3_once, _init_l_Lean_instInhabitedLocalContext_default___closed__3);
v___x_584_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__1, &l_Lean_instInhabitedLocalContext_default___closed__1_once, _init_l_Lean_instInhabitedLocalContext_default___closed__1);
v___x_585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
lean_ctor_set(v___x_585_, 1, v___x_583_);
lean_ctor_set(v___x_585_, 2, v___x_582_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext_default(void){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_instInhabitedLocalContext(void){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_instInhabitedLocalContext_default;
return v___x_587_;
}
}
LEAN_EXPORT lean_object* lean_mk_empty_local_ctx(lean_object* v_x_588_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_unsigned_to_nat(32u);
v___x_590_ = lean_mk_empty_array_with_capacity(v___x_589_);
lean_dec_ref(v___x_590_);
v___x_591_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_LocalContext_empty(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_unsigned_to_nat(32u);
v___x_593_ = lean_mk_empty_array_with_capacity(v___x_592_);
lean_dec_ref(v___x_593_);
v___x_594_ = lean_obj_once(&l_Lean_instInhabitedLocalContext_default___closed__4, &l_Lean_instInhabitedLocalContext_default___closed__4_once, _init_l_Lean_instInhabitedLocalContext_default___closed__4);
return v___x_594_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(lean_object* v_x_595_){
_start:
{
uint8_t v___x_596_; 
v___x_596_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg___boxed(lean_object* v_x_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___redArg(v_x_597_);
lean_dec_ref(v_x_597_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(lean_object* v_00_u03b2_600_, lean_object* v_x_601_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0___boxed(lean_object* v_00_u03b2_603_, lean_object* v_x_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_LocalContext_isEmpty_spec__0(v_00_u03b2_603_, v_x_604_);
lean_dec_ref(v_x_604_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT uint8_t lean_local_ctx_is_empty(lean_object* v_lctx_607_){
_start:
{
lean_object* v_fvarIdToDecl_608_; uint8_t v___x_609_; 
v_fvarIdToDecl_608_ = lean_ctor_get(v_lctx_607_, 0);
lean_inc_ref(v_fvarIdToDecl_608_);
lean_dec_ref(v_lctx_607_);
v___x_609_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fvarIdToDecl_608_);
lean_dec_ref(v_fvarIdToDecl_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isEmpty___boxed(lean_object* v_lctx_610_){
_start:
{
uint8_t v_res_611_; lean_object* v_r_612_; 
v_res_611_ = lean_local_ctx_is_empty(v_lctx_610_);
v_r_612_ = lean_box(v_res_611_);
return v_r_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_x_616_){
_start:
{
lean_object* v_ks_617_; lean_object* v_vs_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_642_; 
v_ks_617_ = lean_ctor_get(v_x_613_, 0);
v_vs_618_ = lean_ctor_get(v_x_613_, 1);
v_isSharedCheck_642_ = !lean_is_exclusive(v_x_613_);
if (v_isSharedCheck_642_ == 0)
{
v___x_620_ = v_x_613_;
v_isShared_621_ = v_isSharedCheck_642_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_vs_618_);
lean_inc(v_ks_617_);
lean_dec(v_x_613_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_642_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_array_get_size(v_ks_617_);
v___x_623_ = lean_nat_dec_lt(v_x_614_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
lean_dec(v_x_614_);
v___x_624_ = lean_array_push(v_ks_617_, v_x_615_);
v___x_625_ = lean_array_push(v_vs_618_, v_x_616_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v___x_625_);
lean_ctor_set(v___x_620_, 0, v___x_624_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
else
{
lean_object* v_k_x27_629_; uint8_t v___x_630_; 
v_k_x27_629_ = lean_array_fget_borrowed(v_ks_617_, v_x_614_);
v___x_630_ = l_Lean_instBEqFVarId_beq(v_x_615_, v_k_x27_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_632_; 
if (v_isShared_621_ == 0)
{
v___x_632_ = v___x_620_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_ks_617_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_vs_618_);
v___x_632_ = v_reuseFailAlloc_636_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = lean_nat_add(v_x_614_, v___x_633_);
lean_dec(v_x_614_);
v_x_613_ = v___x_632_;
v_x_614_ = v___x_634_;
goto _start;
}
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_637_ = lean_array_fset(v_ks_617_, v_x_614_, v_x_615_);
v___x_638_ = lean_array_fset(v_vs_618_, v_x_614_, v_x_616_);
lean_dec(v_x_614_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v___x_638_);
lean_ctor_set(v___x_620_, 0, v___x_637_);
v___x_640_ = v___x_620_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_n_643_, lean_object* v_k_644_, lean_object* v_v_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1_spec__2___redArg(v_n_643_, v___x_646_, v_k_644_, v_v_645_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(lean_object* v_x_649_, size_t v_x_650_, size_t v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
lean_object* v_es_654_; size_t v___x_655_; size_t v___x_656_; lean_object* v_j_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_es_654_ = lean_ctor_get(v_x_649_, 0);
v___x_655_ = ((size_t)31ULL);
v___x_656_ = lean_usize_land(v_x_650_, v___x_655_);
v_j_657_ = lean_usize_to_nat(v___x_656_);
v___x_658_ = lean_array_get_size(v_es_654_);
v___x_659_ = lean_nat_dec_lt(v_j_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_dec(v_j_657_);
lean_dec(v_x_653_);
lean_dec(v_x_652_);
return v_x_649_;
}
else
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_698_; 
lean_inc_ref(v_es_654_);
v_isSharedCheck_698_ = !lean_is_exclusive(v_x_649_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v_x_649_, 0);
lean_dec(v_unused_699_);
v___x_661_ = v_x_649_;
v_isShared_662_ = v_isSharedCheck_698_;
goto v_resetjp_660_;
}
else
{
lean_dec(v_x_649_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_698_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_v_663_; lean_object* v___x_664_; lean_object* v_xs_x27_665_; lean_object* v___y_667_; 
v_v_663_ = lean_array_fget(v_es_654_, v_j_657_);
v___x_664_ = lean_box(0);
v_xs_x27_665_ = lean_array_fset(v_es_654_, v_j_657_, v___x_664_);
switch(lean_obj_tag(v_v_663_))
{
case 0:
{
lean_object* v_key_672_; lean_object* v_val_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_683_; 
v_key_672_ = lean_ctor_get(v_v_663_, 0);
v_val_673_ = lean_ctor_get(v_v_663_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_v_663_);
if (v_isSharedCheck_683_ == 0)
{
v___x_675_ = v_v_663_;
v_isShared_676_ = v_isSharedCheck_683_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_val_673_);
lean_inc(v_key_672_);
lean_dec(v_v_663_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_683_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
uint8_t v___x_677_; 
v___x_677_ = l_Lean_instBEqFVarId_beq(v_x_652_, v_key_672_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_del_object(v___x_675_);
v___x_678_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_672_, v_val_673_, v_x_652_, v_x_653_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
v___y_667_ = v___x_679_;
goto v___jp_666_;
}
else
{
lean_object* v___x_681_; 
lean_dec(v_val_673_);
lean_dec(v_key_672_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v_x_653_);
lean_ctor_set(v___x_675_, 0, v_x_652_);
v___x_681_ = v___x_675_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_x_652_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_x_653_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
v___y_667_ = v___x_681_;
goto v___jp_666_;
}
}
}
}
case 1:
{
lean_object* v_node_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_696_; 
v_node_684_ = lean_ctor_get(v_v_663_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v_v_663_);
if (v_isSharedCheck_696_ == 0)
{
v___x_686_ = v_v_663_;
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_node_684_);
lean_dec(v_v_663_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_688_ = ((size_t)5ULL);
v___x_689_ = lean_usize_shift_right(v_x_650_, v___x_688_);
v___x_690_ = ((size_t)1ULL);
v___x_691_ = lean_usize_add(v_x_651_, v___x_690_);
v___x_692_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_node_684_, v___x_689_, v___x_691_, v_x_652_, v_x_653_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_692_);
v___x_694_ = v___x_686_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
v___y_667_ = v___x_694_;
goto v___jp_666_;
}
}
}
default: 
{
lean_object* v___x_697_; 
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v_x_652_);
lean_ctor_set(v___x_697_, 1, v_x_653_);
v___y_667_ = v___x_697_;
goto v___jp_666_;
}
}
v___jp_666_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = lean_array_fset(v_xs_x27_665_, v_j_657_, v___y_667_);
lean_dec(v_j_657_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_668_);
v___x_670_ = v___x_661_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
else
{
lean_object* v_ks_700_; lean_object* v_vs_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_719_; 
v_ks_700_ = lean_ctor_get(v_x_649_, 0);
v_vs_701_ = lean_ctor_get(v_x_649_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_x_649_);
if (v_isSharedCheck_719_ == 0)
{
v___x_703_ = v_x_649_;
v_isShared_704_ = v_isSharedCheck_719_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_vs_701_);
lean_inc(v_ks_700_);
lean_dec(v_x_649_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_719_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_ks_700_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_vs_701_);
v___x_706_ = v_reuseFailAlloc_718_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v_newNode_707_; size_t v___x_708_; uint8_t v___x_709_; 
v_newNode_707_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__1___redArg(v___x_706_, v_x_652_, v_x_653_);
v___x_708_ = ((size_t)7ULL);
v___x_709_ = lean_usize_dec_le(v___x_708_, v_x_651_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_710_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_707_);
v___x_711_ = lean_unsigned_to_nat(4u);
v___x_712_ = lean_nat_dec_lt(v___x_710_, v___x_711_);
lean_dec(v___x_710_);
if (v___x_712_ == 0)
{
lean_object* v_ks_713_; lean_object* v_vs_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_ks_713_ = lean_ctor_get(v_newNode_707_, 0);
lean_inc_ref(v_ks_713_);
v_vs_714_ = lean_ctor_get(v_newNode_707_, 1);
lean_inc_ref(v_vs_714_);
lean_dec_ref(v_newNode_707_);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg___closed__0);
v___x_717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0_spec__2___redArg(v_x_651_, v_ks_713_, v_vs_714_, v___x_715_, v___x_716_);
lean_dec_ref(v_vs_714_);
lean_dec_ref(v_ks_713_);
return v___x_717_;
}
else
{
return v_newNode_707_;
}
}
else
{
return v_newNode_707_;
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
size_t v_x_361__boxed_752_; size_t v_x_362__boxed_753_; lean_object* v_res_754_; 
v_x_361__boxed_752_ = lean_unbox_usize(v_x_748_);
lean_dec(v_x_748_);
v_x_362__boxed_753_ = lean_unbox_usize(v_x_749_);
lean_dec(v_x_749_);
v_res_754_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0_spec__0___redArg(v_x_747_, v_x_361__boxed_752_, v_x_362__boxed_753_, v_x_750_, v_x_751_);
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
size_t v_x_135__boxed_991_; lean_object* v_res_992_; 
v_x_135__boxed_991_ = lean_unbox_usize(v_x_989_);
lean_dec(v_x_989_);
v_res_992_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0___redArg(v_x_988_, v_x_135__boxed_991_, v_x_990_);
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
size_t v_x_204__boxed_1022_; lean_object* v_res_1023_; 
v_x_204__boxed_1022_ = lean_unbox_usize(v_x_1020_);
lean_dec(v_x_1020_);
v_res_1023_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0_spec__0(v_00_u03b2_1018_, v_x_1019_, v_x_204__boxed_1022_, v_x_1021_);
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
return v___x_1070_;
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
size_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = ((size_t)0ULL);
v___x_1195_ = lean_usize_of_nat(v___x_1192_);
v___x_1196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1190_, v___x_1194_, v___x_1195_, v_x_1189_);
return v___x_1196_;
}
}
else
{
lean_object* v_vs_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_vs_1197_ = lean_ctor_get(v_x_1188_, 0);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_array_get_size(v_vs_1197_);
v___x_1200_ = lean_nat_dec_lt(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
return v_x_1189_;
}
else
{
size_t v___x_1201_; size_t v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = ((size_t)0ULL);
v___x_1202_ = lean_usize_of_nat(v___x_1199_);
v___x_1203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1197_, v___x_1201_, v___x_1202_, v_x_1189_);
return v___x_1203_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(lean_object* v_as_1204_, size_t v_i_1205_, size_t v_stop_1206_, lean_object* v_b_1207_){
_start:
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_usize_dec_eq(v_i_1205_, v_stop_1206_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; 
v___x_1209_ = lean_array_uget_borrowed(v_as_1204_, v_i_1205_);
v___x_1210_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v___x_1209_, v_b_1207_);
v___x_1211_ = ((size_t)1ULL);
v___x_1212_ = lean_usize_add(v_i_1205_, v___x_1211_);
v_i_1205_ = v___x_1212_;
v_b_1207_ = v___x_1210_;
goto _start;
}
else
{
return v_b_1207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1___boxed(lean_object* v_as_1214_, lean_object* v_i_1215_, lean_object* v_stop_1216_, lean_object* v_b_1217_){
_start:
{
size_t v_i_boxed_1218_; size_t v_stop_boxed_1219_; lean_object* v_res_1220_; 
v_i_boxed_1218_ = lean_unbox_usize(v_i_1215_);
lean_dec(v_i_1215_);
v_stop_boxed_1219_ = lean_unbox_usize(v_stop_1216_);
lean_dec(v_stop_1216_);
v_res_1220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_as_1214_, v_i_boxed_1218_, v_stop_boxed_1219_, v_b_1217_);
lean_dec_ref(v_as_1214_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2___boxed(lean_object* v_x_1221_, lean_object* v_x_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_x_1221_, v_x_1222_);
lean_dec_ref(v_x_1221_);
return v_res_1223_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(lean_object* v_x_1225_, size_t v_x_1226_, size_t v_x_1227_, lean_object* v_x_1228_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
lean_object* v_cs_1229_; lean_object* v___x_1230_; size_t v___x_1231_; lean_object* v_j_1232_; lean_object* v___x_1233_; size_t v___x_1234_; size_t v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_cs_1229_ = lean_ctor_get(v_x_1225_, 0);
v___x_1230_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_1231_ = lean_usize_shift_right(v_x_1226_, v_x_1227_);
v_j_1232_ = lean_usize_to_nat(v___x_1231_);
v___x_1233_ = lean_array_get_borrowed(v___x_1230_, v_cs_1229_, v_j_1232_);
v___x_1234_ = ((size_t)1ULL);
v___x_1235_ = lean_usize_shift_left(v___x_1234_, v_x_1227_);
v___x_1236_ = lean_usize_sub(v___x_1235_, v___x_1234_);
v___x_1237_ = lean_usize_land(v_x_1226_, v___x_1236_);
v___x_1238_ = ((size_t)5ULL);
v___x_1239_ = lean_usize_sub(v_x_1227_, v___x_1238_);
v___x_1240_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v___x_1233_, v___x_1237_, v___x_1239_, v_x_1228_);
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_add(v_j_1232_, v___x_1241_);
lean_dec(v_j_1232_);
v___x_1243_ = lean_array_get_size(v_cs_1229_);
v___x_1244_ = lean_nat_dec_lt(v___x_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_dec(v___x_1242_);
return v___x_1240_;
}
else
{
size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_usize_of_nat(v___x_1242_);
lean_dec(v___x_1242_);
v___x_1246_ = lean_usize_of_nat(v___x_1243_);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0_spec__1(v_cs_1229_, v___x_1245_, v___x_1246_, v___x_1240_);
return v___x_1247_;
}
}
else
{
lean_object* v_vs_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_vs_1248_ = lean_ctor_get(v_x_1225_, 0);
v___x_1249_ = lean_usize_to_nat(v_x_1226_);
v___x_1250_ = lean_array_get_size(v_vs_1248_);
v___x_1251_ = lean_nat_dec_lt(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec(v___x_1249_);
return v_x_1228_;
}
else
{
size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_usize_of_nat(v___x_1249_);
lean_dec(v___x_1249_);
v___x_1253_ = lean_usize_of_nat(v___x_1250_);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_vs_1248_, v___x_1252_, v___x_1253_, v_x_1228_);
return v___x_1254_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___boxed(lean_object* v_x_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
size_t v_x_1260__boxed_1259_; size_t v_x_1261__boxed_1260_; lean_object* v_res_1261_; 
v_x_1260__boxed_1259_ = lean_unbox_usize(v_x_1256_);
lean_dec(v_x_1256_);
v_x_1261__boxed_1260_ = lean_unbox_usize(v_x_1257_);
lean_dec(v_x_1257_);
v_res_1261_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_x_1255_, v_x_1260__boxed_1259_, v_x_1261__boxed_1260_, v_x_1258_);
lean_dec_ref(v_x_1255_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(lean_object* v_t_1262_, lean_object* v_init_1263_, lean_object* v_start_1264_){
_start:
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = lean_nat_dec_eq(v_start_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v_root_1267_; lean_object* v_tail_1268_; size_t v_shift_1269_; lean_object* v_tailOff_1270_; uint8_t v___x_1271_; 
v_root_1267_ = lean_ctor_get(v_t_1262_, 0);
v_tail_1268_ = lean_ctor_get(v_t_1262_, 1);
v_shift_1269_ = lean_ctor_get_usize(v_t_1262_, 4);
v_tailOff_1270_ = lean_ctor_get(v_t_1262_, 3);
v___x_1271_ = lean_nat_dec_le(v_tailOff_1270_, v_start_1264_);
if (v___x_1271_ == 0)
{
size_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1272_ = lean_usize_of_nat(v_start_1264_);
v___x_1273_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0(v_root_1267_, v___x_1272_, v_shift_1269_, v_init_1263_);
v___x_1274_ = lean_array_get_size(v_tail_1268_);
v___x_1275_ = lean_nat_dec_lt(v___x_1265_, v___x_1274_);
if (v___x_1275_ == 0)
{
return v___x_1273_;
}
else
{
size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = ((size_t)0ULL);
v___x_1277_ = lean_usize_of_nat(v___x_1274_);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1268_, v___x_1276_, v___x_1277_, v___x_1273_);
return v___x_1278_;
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = lean_nat_sub(v_start_1264_, v_tailOff_1270_);
v___x_1280_ = lean_array_get_size(v_tail_1268_);
v___x_1281_ = lean_nat_dec_lt(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_dec(v___x_1279_);
return v_init_1263_;
}
else
{
size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_usize_of_nat(v___x_1279_);
lean_dec(v___x_1279_);
v___x_1283_ = lean_usize_of_nat(v___x_1280_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1268_, v___x_1282_, v___x_1283_, v_init_1263_);
return v___x_1284_;
}
}
}
else
{
lean_object* v_root_1285_; lean_object* v_tail_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_root_1285_ = lean_ctor_get(v_t_1262_, 0);
v_tail_1286_ = lean_ctor_get(v_t_1262_, 1);
v___x_1287_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__2(v_root_1285_, v_init_1263_);
v___x_1288_ = lean_array_get_size(v_tail_1286_);
v___x_1289_ = lean_nat_dec_lt(v___x_1265_, v___x_1288_);
if (v___x_1289_ == 0)
{
return v___x_1287_;
}
else
{
size_t v___x_1290_; size_t v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = ((size_t)0ULL);
v___x_1291_ = lean_usize_of_nat(v___x_1288_);
v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__1(v_tail_1286_, v___x_1290_, v___x_1291_, v___x_1287_);
return v___x_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0___boxed(lean_object* v_t_1293_, lean_object* v_init_1294_, lean_object* v_start_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_t_1293_, v_init_1294_, v_start_1295_);
lean_dec(v_start_1295_);
lean_dec_ref(v_t_1293_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds(lean_object* v_lctx_1299_){
_start:
{
lean_object* v_decls_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_decls_1300_ = lean_ctor_get(v_lctx_1299_, 1);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = ((lean_object*)(l_Lean_LocalContext_getFVarIds___closed__0));
v___x_1303_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0(v_decls_1300_, v___x_1302_, v___x_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVarIds___boxed(lean_object* v_lctx_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_LocalContext_getFVarIds(v_lctx_1304_);
lean_dec_ref(v_lctx_1304_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(size_t v_sz_1306_, size_t v_i_1307_, lean_object* v_bs_1308_){
_start:
{
uint8_t v___x_1309_; 
v___x_1309_ = lean_usize_dec_lt(v_i_1307_, v_sz_1306_);
if (v___x_1309_ == 0)
{
return v_bs_1308_;
}
else
{
lean_object* v_v_1310_; lean_object* v___x_1311_; lean_object* v_bs_x27_1312_; lean_object* v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; lean_object* v___x_1316_; 
v_v_1310_ = lean_array_uget(v_bs_1308_, v_i_1307_);
v___x_1311_ = lean_unsigned_to_nat(0u);
v_bs_x27_1312_ = lean_array_uset(v_bs_1308_, v_i_1307_, v___x_1311_);
v___x_1313_ = l_Lean_mkFVar(v_v_1310_);
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = lean_usize_add(v_i_1307_, v___x_1314_);
v___x_1316_ = lean_array_uset(v_bs_x27_1312_, v_i_1307_, v___x_1313_);
v_i_1307_ = v___x_1315_;
v_bs_1308_ = v___x_1316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0___boxed(lean_object* v_sz_1318_, lean_object* v_i_1319_, lean_object* v_bs_1320_){
_start:
{
size_t v_sz_boxed_1321_; size_t v_i_boxed_1322_; lean_object* v_res_1323_; 
v_sz_boxed_1321_ = lean_unbox_usize(v_sz_1318_);
lean_dec(v_sz_1318_);
v_i_boxed_1322_ = lean_unbox_usize(v_i_1319_);
lean_dec(v_i_1319_);
v_res_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_boxed_1321_, v_i_boxed_1322_, v_bs_1320_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars(lean_object* v_lctx_1324_){
_start:
{
lean_object* v___x_1325_; size_t v_sz_1326_; size_t v___x_1327_; lean_object* v___x_1328_; 
v___x_1325_ = l_Lean_LocalContext_getFVarIds(v_lctx_1324_);
v_sz_1326_ = lean_array_size(v___x_1325_);
v___x_1327_ = ((size_t)0ULL);
v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_getFVars_spec__0(v_sz_1326_, v___x_1327_, v___x_1325_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFVars___boxed(lean_object* v_lctx_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_LocalContext_getFVars(v_lctx_1329_);
lean_dec_ref(v_lctx_1329_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(lean_object* v_a_1331_){
_start:
{
lean_object* v_size_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v_size_1332_ = lean_ctor_get(v_a_1331_, 2);
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_nat_dec_eq(v_size_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1335_ = lean_box(0);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_sub(v_size_1332_, v___x_1336_);
v___x_1338_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1335_, v_a_1331_, v___x_1337_);
lean_dec(v___x_1337_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_PersistentArray_pop___redArg(v_a_1331_);
v_a_1331_ = v___x_1339_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1338_, 1);
return v_a_1331_;
}
}
else
{
return v_a_1331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(lean_object* v_k_1341_, lean_object* v_t_1342_){
_start:
{
if (lean_obj_tag(v_t_1342_) == 0)
{
lean_object* v_k_1343_; lean_object* v_v_1344_; lean_object* v_l_1345_; lean_object* v_r_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_2000_; 
v_k_1343_ = lean_ctor_get(v_t_1342_, 1);
v_v_1344_ = lean_ctor_get(v_t_1342_, 2);
v_l_1345_ = lean_ctor_get(v_t_1342_, 3);
v_r_1346_ = lean_ctor_get(v_t_1342_, 4);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_t_1342_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v_t_1342_, 0);
lean_dec(v_unused_2001_);
v___x_1348_ = v_t_1342_;
v_isShared_1349_ = v_isSharedCheck_2000_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_r_1346_);
lean_inc(v_l_1345_);
lean_inc(v_v_1344_);
lean_inc(v_k_1343_);
lean_dec(v_t_1342_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_2000_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
uint8_t v___x_1350_; 
v___x_1350_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1341_, v_k_1343_);
switch(v___x_1350_)
{
case 0:
{
lean_object* v_impl_1351_; lean_object* v___x_1352_; 
v_impl_1351_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1341_, v_l_1345_);
v___x_1352_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1351_) == 0)
{
if (lean_obj_tag(v_r_1346_) == 0)
{
lean_object* v_size_1353_; lean_object* v_size_1354_; lean_object* v_k_1355_; lean_object* v_v_1356_; lean_object* v_l_1357_; lean_object* v_r_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_size_1353_ = lean_ctor_get(v_impl_1351_, 0);
lean_inc(v_size_1353_);
v_size_1354_ = lean_ctor_get(v_r_1346_, 0);
v_k_1355_ = lean_ctor_get(v_r_1346_, 1);
v_v_1356_ = lean_ctor_get(v_r_1346_, 2);
v_l_1357_ = lean_ctor_get(v_r_1346_, 3);
lean_inc(v_l_1357_);
v_r_1358_ = lean_ctor_get(v_r_1346_, 4);
v___x_1359_ = lean_unsigned_to_nat(3u);
v___x_1360_ = lean_nat_mul(v___x_1359_, v_size_1353_);
v___x_1361_ = lean_nat_dec_lt(v___x_1360_, v_size_1354_);
lean_dec(v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
lean_dec(v_l_1357_);
v___x_1362_ = lean_nat_add(v___x_1352_, v_size_1353_);
lean_dec(v_size_1353_);
v___x_1363_ = lean_nat_add(v___x_1362_, v_size_1354_);
lean_dec(v___x_1362_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 3, v_impl_1351_);
lean_ctor_set(v___x_1348_, 0, v___x_1363_);
v___x_1365_ = v___x_1348_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_impl_1351_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_r_1346_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
else
{
lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1430_; 
lean_inc(v_r_1358_);
lean_inc(v_v_1356_);
lean_inc(v_k_1355_);
lean_inc(v_size_1354_);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_r_1346_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; lean_object* v_unused_1432_; lean_object* v_unused_1433_; lean_object* v_unused_1434_; lean_object* v_unused_1435_; 
v_unused_1431_ = lean_ctor_get(v_r_1346_, 4);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_r_1346_, 3);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_r_1346_, 2);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_r_1346_, 1);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_r_1346_, 0);
lean_dec(v_unused_1435_);
v___x_1368_ = v_r_1346_;
v_isShared_1369_ = v_isSharedCheck_1430_;
goto v_resetjp_1367_;
}
else
{
lean_dec(v_r_1346_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1430_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_size_1370_; lean_object* v_k_1371_; lean_object* v_v_1372_; lean_object* v_l_1373_; lean_object* v_r_1374_; lean_object* v_size_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v_size_1370_ = lean_ctor_get(v_l_1357_, 0);
v_k_1371_ = lean_ctor_get(v_l_1357_, 1);
v_v_1372_ = lean_ctor_get(v_l_1357_, 2);
v_l_1373_ = lean_ctor_get(v_l_1357_, 3);
v_r_1374_ = lean_ctor_get(v_l_1357_, 4);
v_size_1375_ = lean_ctor_get(v_r_1358_, 0);
v___x_1376_ = lean_unsigned_to_nat(2u);
v___x_1377_ = lean_nat_mul(v___x_1376_, v_size_1375_);
v___x_1378_ = lean_nat_dec_lt(v_size_1370_, v___x_1377_);
lean_dec(v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1406_; 
lean_inc(v_r_1374_);
lean_inc(v_l_1373_);
lean_inc(v_v_1372_);
lean_inc(v_k_1371_);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_l_1357_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; lean_object* v_unused_1408_; lean_object* v_unused_1409_; lean_object* v_unused_1410_; lean_object* v_unused_1411_; 
v_unused_1407_ = lean_ctor_get(v_l_1357_, 4);
lean_dec(v_unused_1407_);
v_unused_1408_ = lean_ctor_get(v_l_1357_, 3);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_l_1357_, 2);
lean_dec(v_unused_1409_);
v_unused_1410_ = lean_ctor_get(v_l_1357_, 1);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v_l_1357_, 0);
lean_dec(v_unused_1411_);
v___x_1380_ = v_l_1357_;
v_isShared_1381_ = v_isSharedCheck_1406_;
goto v_resetjp_1379_;
}
else
{
lean_dec(v_l_1357_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1406_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1396_; 
v___x_1382_ = lean_nat_add(v___x_1352_, v_size_1353_);
lean_dec(v_size_1353_);
v___x_1383_ = lean_nat_add(v___x_1382_, v_size_1354_);
lean_dec(v_size_1354_);
if (lean_obj_tag(v_l_1373_) == 0)
{
lean_object* v_size_1404_; 
v_size_1404_ = lean_ctor_get(v_l_1373_, 0);
lean_inc(v_size_1404_);
v___y_1396_ = v_size_1404_;
goto v___jp_1395_;
}
else
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_unsigned_to_nat(0u);
v___y_1396_ = v___x_1405_;
goto v___jp_1395_;
}
v___jp_1384_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = lean_nat_add(v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec(v___y_1386_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 4, v_r_1358_);
lean_ctor_set(v___x_1380_, 3, v_r_1374_);
lean_ctor_set(v___x_1380_, 2, v_v_1356_);
lean_ctor_set(v___x_1380_, 1, v_k_1355_);
lean_ctor_set(v___x_1380_, 0, v___x_1388_);
v___x_1390_ = v___x_1380_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_r_1374_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_r_1358_);
v___x_1390_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1392_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v___x_1390_);
lean_ctor_set(v___x_1368_, 3, v___y_1385_);
lean_ctor_set(v___x_1368_, 2, v_v_1372_);
lean_ctor_set(v___x_1368_, 1, v_k_1371_);
lean_ctor_set(v___x_1368_, 0, v___x_1383_);
v___x_1392_ = v___x_1368_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v___y_1385_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
v___jp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = lean_nat_add(v___x_1382_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec(v___x_1382_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v_l_1373_);
lean_ctor_set(v___x_1348_, 3, v_impl_1351_);
lean_ctor_set(v___x_1348_, 0, v___x_1397_);
v___x_1399_ = v___x_1348_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_impl_1351_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_l_1373_);
v___x_1399_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_nat_add(v___x_1352_, v_size_1375_);
if (lean_obj_tag(v_r_1374_) == 0)
{
lean_object* v_size_1401_; 
v_size_1401_ = lean_ctor_get(v_r_1374_, 0);
lean_inc(v_size_1401_);
v___y_1385_ = v___x_1399_;
v___y_1386_ = v___x_1400_;
v___y_1387_ = v_size_1401_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_unsigned_to_nat(0u);
v___y_1385_ = v___x_1399_;
v___y_1386_ = v___x_1400_;
v___y_1387_ = v___x_1402_;
goto v___jp_1384_;
}
}
}
}
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
lean_del_object(v___x_1348_);
v___x_1412_ = lean_nat_add(v___x_1352_, v_size_1353_);
lean_dec(v_size_1353_);
v___x_1413_ = lean_nat_add(v___x_1412_, v_size_1354_);
lean_dec(v_size_1354_);
v___x_1414_ = lean_nat_add(v___x_1412_, v_size_1370_);
lean_dec(v___x_1412_);
lean_inc_ref(v_impl_1351_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 4, v_l_1357_);
lean_ctor_set(v___x_1368_, 3, v_impl_1351_);
lean_ctor_set(v___x_1368_, 2, v_v_1344_);
lean_ctor_set(v___x_1368_, 1, v_k_1343_);
lean_ctor_set(v___x_1368_, 0, v___x_1414_);
v___x_1416_ = v___x_1368_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v_impl_1351_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v_l_1357_);
v___x_1416_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_isSharedCheck_1423_ = !lean_is_exclusive(v_impl_1351_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; lean_object* v_unused_1425_; lean_object* v_unused_1426_; lean_object* v_unused_1427_; lean_object* v_unused_1428_; 
v_unused_1424_ = lean_ctor_get(v_impl_1351_, 4);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v_impl_1351_, 3);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v_impl_1351_, 2);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_impl_1351_, 1);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_impl_1351_, 0);
lean_dec(v_unused_1428_);
v___x_1418_ = v_impl_1351_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v_impl_1351_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 4, v_r_1358_);
lean_ctor_set(v___x_1418_, 3, v___x_1416_);
lean_ctor_set(v___x_1418_, 2, v_v_1356_);
lean_ctor_set(v___x_1418_, 1, v_k_1355_);
lean_ctor_set(v___x_1418_, 0, v___x_1413_);
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_k_1355_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_v_1356_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_r_1358_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v_size_1436_ = lean_ctor_get(v_impl_1351_, 0);
lean_inc(v_size_1436_);
v___x_1437_ = lean_nat_add(v___x_1352_, v_size_1436_);
lean_dec(v_size_1436_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 3, v_impl_1351_);
lean_ctor_set(v___x_1348_, 0, v___x_1437_);
v___x_1439_ = v___x_1348_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_impl_1351_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v_r_1346_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
else
{
if (lean_obj_tag(v_r_1346_) == 0)
{
lean_object* v_l_1441_; 
v_l_1441_ = lean_ctor_get(v_r_1346_, 3);
lean_inc(v_l_1441_);
if (lean_obj_tag(v_l_1441_) == 0)
{
lean_object* v_r_1442_; 
v_r_1442_ = lean_ctor_get(v_r_1346_, 4);
lean_inc(v_r_1442_);
if (lean_obj_tag(v_r_1442_) == 0)
{
lean_object* v_size_1443_; lean_object* v_k_1444_; lean_object* v_v_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1458_; 
v_size_1443_ = lean_ctor_get(v_r_1346_, 0);
v_k_1444_ = lean_ctor_get(v_r_1346_, 1);
v_v_1445_ = lean_ctor_get(v_r_1346_, 2);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_r_1346_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; lean_object* v_unused_1460_; 
v_unused_1459_ = lean_ctor_get(v_r_1346_, 4);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_r_1346_, 3);
lean_dec(v_unused_1460_);
v___x_1447_ = v_r_1346_;
v_isShared_1448_ = v_isSharedCheck_1458_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_v_1445_);
lean_inc(v_k_1444_);
lean_inc(v_size_1443_);
lean_dec(v_r_1346_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1458_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v_size_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
v_size_1449_ = lean_ctor_get(v_l_1441_, 0);
v___x_1450_ = lean_nat_add(v___x_1352_, v_size_1443_);
lean_dec(v_size_1443_);
v___x_1451_ = lean_nat_add(v___x_1352_, v_size_1449_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 4, v_l_1441_);
lean_ctor_set(v___x_1447_, 3, v_impl_1351_);
lean_ctor_set(v___x_1447_, 2, v_v_1344_);
lean_ctor_set(v___x_1447_, 1, v_k_1343_);
lean_ctor_set(v___x_1447_, 0, v___x_1451_);
v___x_1453_ = v___x_1447_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_impl_1351_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_l_1441_);
v___x_1453_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1455_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v_r_1442_);
lean_ctor_set(v___x_1348_, 3, v___x_1453_);
lean_ctor_set(v___x_1348_, 2, v_v_1445_);
lean_ctor_set(v___x_1348_, 1, v_k_1444_);
lean_ctor_set(v___x_1348_, 0, v___x_1450_);
v___x_1455_ = v___x_1348_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_k_1444_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_v_1445_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v_r_1442_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_k_1461_; lean_object* v_v_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1485_; 
v_k_1461_ = lean_ctor_get(v_r_1346_, 1);
v_v_1462_ = lean_ctor_get(v_r_1346_, 2);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_r_1346_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; 
v_unused_1486_ = lean_ctor_get(v_r_1346_, 4);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_r_1346_, 3);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_r_1346_, 0);
lean_dec(v_unused_1488_);
v___x_1464_ = v_r_1346_;
v_isShared_1465_ = v_isSharedCheck_1485_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_v_1462_);
lean_inc(v_k_1461_);
lean_dec(v_r_1346_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1485_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v_k_1466_; lean_object* v_v_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1481_; 
v_k_1466_ = lean_ctor_get(v_l_1441_, 1);
v_v_1467_ = lean_ctor_get(v_l_1441_, 2);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_l_1441_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; 
v_unused_1482_ = lean_ctor_get(v_l_1441_, 4);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_l_1441_, 3);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_l_1441_, 0);
lean_dec(v_unused_1484_);
v___x_1469_ = v_l_1441_;
v_isShared_1470_ = v_isSharedCheck_1481_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_v_1467_);
lean_inc(v_k_1466_);
lean_dec(v_l_1441_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1481_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1471_ = lean_unsigned_to_nat(3u);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 4, v_r_1442_);
lean_ctor_set(v___x_1469_, 3, v_r_1442_);
lean_ctor_set(v___x_1469_, 2, v_v_1344_);
lean_ctor_set(v___x_1469_, 1, v_k_1343_);
lean_ctor_set(v___x_1469_, 0, v___x_1352_);
v___x_1473_ = v___x_1469_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_r_1442_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_r_1442_);
v___x_1473_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1475_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 3, v_r_1442_);
lean_ctor_set(v___x_1464_, 0, v___x_1352_);
v___x_1475_ = v___x_1464_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_k_1461_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_v_1462_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_r_1442_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_r_1442_);
v___x_1475_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v___x_1475_);
lean_ctor_set(v___x_1348_, 3, v___x_1473_);
lean_ctor_set(v___x_1348_, 2, v_v_1467_);
lean_ctor_set(v___x_1348_, 1, v_k_1466_);
lean_ctor_set(v___x_1348_, 0, v___x_1471_);
v___x_1477_ = v___x_1348_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1466_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1467_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1489_; 
v_r_1489_ = lean_ctor_get(v_r_1346_, 4);
lean_inc(v_r_1489_);
if (lean_obj_tag(v_r_1489_) == 0)
{
lean_object* v_k_1490_; lean_object* v_v_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1502_; 
v_k_1490_ = lean_ctor_get(v_r_1346_, 1);
v_v_1491_ = lean_ctor_get(v_r_1346_, 2);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_r_1346_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; 
v_unused_1503_ = lean_ctor_get(v_r_1346_, 4);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_r_1346_, 3);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_r_1346_, 0);
lean_dec(v_unused_1505_);
v___x_1493_ = v_r_1346_;
v_isShared_1494_ = v_isSharedCheck_1502_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_v_1491_);
lean_inc(v_k_1490_);
lean_dec(v_r_1346_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1502_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_unsigned_to_nat(3u);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 4, v_l_1441_);
lean_ctor_set(v___x_1493_, 2, v_v_1344_);
lean_ctor_set(v___x_1493_, 1, v_k_1343_);
lean_ctor_set(v___x_1493_, 0, v___x_1352_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_l_1441_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_l_1441_);
v___x_1497_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v_r_1489_);
lean_ctor_set(v___x_1348_, 3, v___x_1497_);
lean_ctor_set(v___x_1348_, 2, v_v_1491_);
lean_ctor_set(v___x_1348_, 1, v_k_1490_);
lean_ctor_set(v___x_1348_, 0, v___x_1495_);
v___x_1499_ = v___x_1348_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1490_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1491_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_r_1489_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v_size_1506_; lean_object* v_k_1507_; lean_object* v_v_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1519_; 
v_size_1506_ = lean_ctor_get(v_r_1346_, 0);
v_k_1507_ = lean_ctor_get(v_r_1346_, 1);
v_v_1508_ = lean_ctor_get(v_r_1346_, 2);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_r_1346_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; lean_object* v_unused_1521_; 
v_unused_1520_ = lean_ctor_get(v_r_1346_, 4);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_r_1346_, 3);
lean_dec(v_unused_1521_);
v___x_1510_ = v_r_1346_;
v_isShared_1511_ = v_isSharedCheck_1519_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_v_1508_);
lean_inc(v_k_1507_);
lean_inc(v_size_1506_);
lean_dec(v_r_1346_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1519_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 3, v_r_1489_);
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_size_1506_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1507_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1508_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_r_1489_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_r_1489_);
v___x_1513_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1514_ = lean_unsigned_to_nat(2u);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v___x_1513_);
lean_ctor_set(v___x_1348_, 3, v_r_1489_);
lean_ctor_set(v___x_1348_, 0, v___x_1514_);
v___x_1516_ = v___x_1348_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_r_1489_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v___x_1513_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
else
{
lean_object* v___x_1523_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 3, v_r_1346_);
lean_ctor_set(v___x_1348_, 0, v___x_1352_);
v___x_1523_ = v___x_1348_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_r_1346_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_r_1346_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1348_);
lean_dec(v_v_1344_);
lean_dec(v_k_1343_);
if (lean_obj_tag(v_l_1345_) == 0)
{
if (lean_obj_tag(v_r_1346_) == 0)
{
lean_object* v_size_1525_; lean_object* v_k_1526_; lean_object* v_v_1527_; lean_object* v_l_1528_; lean_object* v_r_1529_; lean_object* v_size_1530_; lean_object* v_k_1531_; lean_object* v_v_1532_; lean_object* v_l_1533_; lean_object* v_r_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v_size_1525_ = lean_ctor_get(v_l_1345_, 0);
v_k_1526_ = lean_ctor_get(v_l_1345_, 1);
v_v_1527_ = lean_ctor_get(v_l_1345_, 2);
v_l_1528_ = lean_ctor_get(v_l_1345_, 3);
v_r_1529_ = lean_ctor_get(v_l_1345_, 4);
lean_inc(v_r_1529_);
v_size_1530_ = lean_ctor_get(v_r_1346_, 0);
v_k_1531_ = lean_ctor_get(v_r_1346_, 1);
v_v_1532_ = lean_ctor_get(v_r_1346_, 2);
v_l_1533_ = lean_ctor_get(v_r_1346_, 3);
lean_inc(v_l_1533_);
v_r_1534_ = lean_ctor_get(v_r_1346_, 4);
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_nat_dec_lt(v_size_1525_, v_size_1530_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1672_; 
lean_inc(v_l_1528_);
lean_inc(v_v_1527_);
lean_inc(v_k_1526_);
v_isSharedCheck_1672_ = !lean_is_exclusive(v_l_1345_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; lean_object* v_unused_1674_; lean_object* v_unused_1675_; lean_object* v_unused_1676_; lean_object* v_unused_1677_; 
v_unused_1673_ = lean_ctor_get(v_l_1345_, 4);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_l_1345_, 3);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_l_1345_, 2);
lean_dec(v_unused_1675_);
v_unused_1676_ = lean_ctor_get(v_l_1345_, 1);
lean_dec(v_unused_1676_);
v_unused_1677_ = lean_ctor_get(v_l_1345_, 0);
lean_dec(v_unused_1677_);
v___x_1538_ = v_l_1345_;
v_isShared_1539_ = v_isSharedCheck_1672_;
goto v_resetjp_1537_;
}
else
{
lean_dec(v_l_1345_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1672_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v_tree_1541_; 
v___x_1540_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1526_, v_v_1527_, v_l_1528_, v_r_1529_);
v_tree_1541_ = lean_ctor_get(v___x_1540_, 2);
lean_inc(v_tree_1541_);
if (lean_obj_tag(v_tree_1541_) == 0)
{
lean_object* v_k_1542_; lean_object* v_v_1543_; lean_object* v_size_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v_k_1542_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_k_1542_);
v_v_1543_ = lean_ctor_get(v___x_1540_, 1);
lean_inc(v_v_1543_);
lean_dec_ref(v___x_1540_);
v_size_1544_ = lean_ctor_get(v_tree_1541_, 0);
v___x_1545_ = lean_unsigned_to_nat(3u);
v___x_1546_ = lean_nat_mul(v___x_1545_, v_size_1544_);
v___x_1547_ = lean_nat_dec_lt(v___x_1546_, v_size_1530_);
lean_dec(v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_dec(v_l_1533_);
v___x_1548_ = lean_nat_add(v___x_1535_, v_size_1544_);
v___x_1549_ = lean_nat_add(v___x_1548_, v_size_1530_);
lean_dec(v___x_1548_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v_r_1346_);
lean_ctor_set(v___x_1538_, 3, v_tree_1541_);
lean_ctor_set(v___x_1538_, 2, v_v_1543_);
lean_ctor_set(v___x_1538_, 1, v_k_1542_);
lean_ctor_set(v___x_1538_, 0, v___x_1549_);
v___x_1551_ = v___x_1538_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_k_1542_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_v_1543_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_tree_1541_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v_r_1346_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
else
{
lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1607_; 
lean_inc(v_r_1534_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
lean_inc(v_size_1530_);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_r_1346_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; lean_object* v_unused_1609_; lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; 
v_unused_1608_ = lean_ctor_get(v_r_1346_, 4);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_r_1346_, 3);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_r_1346_, 2);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_r_1346_, 1);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_r_1346_, 0);
lean_dec(v_unused_1612_);
v___x_1554_ = v_r_1346_;
v_isShared_1555_ = v_isSharedCheck_1607_;
goto v_resetjp_1553_;
}
else
{
lean_dec(v_r_1346_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1607_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_size_1556_; lean_object* v_k_1557_; lean_object* v_v_1558_; lean_object* v_l_1559_; lean_object* v_r_1560_; lean_object* v_size_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_size_1556_ = lean_ctor_get(v_l_1533_, 0);
v_k_1557_ = lean_ctor_get(v_l_1533_, 1);
v_v_1558_ = lean_ctor_get(v_l_1533_, 2);
v_l_1559_ = lean_ctor_get(v_l_1533_, 3);
v_r_1560_ = lean_ctor_get(v_l_1533_, 4);
v_size_1561_ = lean_ctor_get(v_r_1534_, 0);
v___x_1562_ = lean_unsigned_to_nat(2u);
v___x_1563_ = lean_nat_mul(v___x_1562_, v_size_1561_);
v___x_1564_ = lean_nat_dec_lt(v_size_1556_, v___x_1563_);
lean_dec(v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1592_; 
lean_inc(v_r_1560_);
lean_inc(v_l_1559_);
lean_inc(v_v_1558_);
lean_inc(v_k_1557_);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_l_1533_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; lean_object* v_unused_1596_; lean_object* v_unused_1597_; 
v_unused_1593_ = lean_ctor_get(v_l_1533_, 4);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_l_1533_, 3);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_l_1533_, 2);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_l_1533_, 1);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_l_1533_, 0);
lean_dec(v_unused_1597_);
v___x_1566_ = v_l_1533_;
v_isShared_1567_ = v_isSharedCheck_1592_;
goto v_resetjp_1565_;
}
else
{
lean_dec(v_l_1533_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1592_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1582_; 
v___x_1568_ = lean_nat_add(v___x_1535_, v_size_1544_);
v___x_1569_ = lean_nat_add(v___x_1568_, v_size_1530_);
lean_dec(v_size_1530_);
if (lean_obj_tag(v_l_1559_) == 0)
{
lean_object* v_size_1590_; 
v_size_1590_ = lean_ctor_get(v_l_1559_, 0);
lean_inc(v_size_1590_);
v___y_1582_ = v_size_1590_;
goto v___jp_1581_;
}
else
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_unsigned_to_nat(0u);
v___y_1582_ = v___x_1591_;
goto v___jp_1581_;
}
v___jp_1570_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = lean_nat_add(v___y_1571_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec(v___y_1571_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 4, v_r_1534_);
lean_ctor_set(v___x_1566_, 3, v_r_1560_);
lean_ctor_set(v___x_1566_, 2, v_v_1532_);
lean_ctor_set(v___x_1566_, 1, v_k_1531_);
lean_ctor_set(v___x_1566_, 0, v___x_1574_);
v___x_1576_ = v___x_1566_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_r_1560_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_r_1534_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1578_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 4, v___x_1576_);
lean_ctor_set(v___x_1554_, 3, v___y_1572_);
lean_ctor_set(v___x_1554_, 2, v_v_1558_);
lean_ctor_set(v___x_1554_, 1, v_k_1557_);
lean_ctor_set(v___x_1554_, 0, v___x_1569_);
v___x_1578_ = v___x_1554_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_k_1557_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_v_1558_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v___y_1572_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
v___jp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = lean_nat_add(v___x_1568_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec(v___x_1568_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v_l_1559_);
lean_ctor_set(v___x_1538_, 3, v_tree_1541_);
lean_ctor_set(v___x_1538_, 2, v_v_1543_);
lean_ctor_set(v___x_1538_, 1, v_k_1542_);
lean_ctor_set(v___x_1538_, 0, v___x_1583_);
v___x_1585_ = v___x_1538_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_k_1542_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_v_1543_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v_tree_1541_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v_l_1559_);
v___x_1585_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_nat_add(v___x_1535_, v_size_1561_);
if (lean_obj_tag(v_r_1560_) == 0)
{
lean_object* v_size_1587_; 
v_size_1587_ = lean_ctor_get(v_r_1560_, 0);
lean_inc(v_size_1587_);
v___y_1571_ = v___x_1586_;
v___y_1572_ = v___x_1585_;
v___y_1573_ = v_size_1587_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_unsigned_to_nat(0u);
v___y_1571_ = v___x_1586_;
v___y_1572_ = v___x_1585_;
v___y_1573_ = v___x_1588_;
goto v___jp_1570_;
}
}
}
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1598_ = lean_nat_add(v___x_1535_, v_size_1544_);
v___x_1599_ = lean_nat_add(v___x_1598_, v_size_1530_);
lean_dec(v_size_1530_);
v___x_1600_ = lean_nat_add(v___x_1598_, v_size_1556_);
lean_dec(v___x_1598_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 4, v_l_1533_);
lean_ctor_set(v___x_1554_, 3, v_tree_1541_);
lean_ctor_set(v___x_1554_, 2, v_v_1543_);
lean_ctor_set(v___x_1554_, 1, v_k_1542_);
lean_ctor_set(v___x_1554_, 0, v___x_1600_);
v___x_1602_ = v___x_1554_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_k_1542_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_v_1543_);
lean_ctor_set(v_reuseFailAlloc_1606_, 3, v_tree_1541_);
lean_ctor_set(v_reuseFailAlloc_1606_, 4, v_l_1533_);
v___x_1602_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1604_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v_r_1534_);
lean_ctor_set(v___x_1538_, 3, v___x_1602_);
lean_ctor_set(v___x_1538_, 2, v_v_1532_);
lean_ctor_set(v___x_1538_, 1, v_k_1531_);
lean_ctor_set(v___x_1538_, 0, v___x_1599_);
v___x_1604_ = v___x_1538_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_r_1534_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
}
else
{
lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1666_; 
lean_inc(v_r_1534_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
lean_inc(v_size_1530_);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_r_1346_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; lean_object* v_unused_1668_; lean_object* v_unused_1669_; lean_object* v_unused_1670_; lean_object* v_unused_1671_; 
v_unused_1667_ = lean_ctor_get(v_r_1346_, 4);
lean_dec(v_unused_1667_);
v_unused_1668_ = lean_ctor_get(v_r_1346_, 3);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_r_1346_, 2);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_r_1346_, 1);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_r_1346_, 0);
lean_dec(v_unused_1671_);
v___x_1614_ = v_r_1346_;
v_isShared_1615_ = v_isSharedCheck_1666_;
goto v_resetjp_1613_;
}
else
{
lean_dec(v_r_1346_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1666_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
if (lean_obj_tag(v_l_1533_) == 0)
{
if (lean_obj_tag(v_r_1534_) == 0)
{
lean_object* v_k_1616_; lean_object* v_v_1617_; lean_object* v_size_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v_k_1616_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_k_1616_);
v_v_1617_ = lean_ctor_get(v___x_1540_, 1);
lean_inc(v_v_1617_);
lean_dec_ref(v___x_1540_);
v_size_1618_ = lean_ctor_get(v_l_1533_, 0);
v___x_1619_ = lean_nat_add(v___x_1535_, v_size_1530_);
lean_dec(v_size_1530_);
v___x_1620_ = lean_nat_add(v___x_1535_, v_size_1618_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 4, v_l_1533_);
lean_ctor_set(v___x_1614_, 3, v_tree_1541_);
lean_ctor_set(v___x_1614_, 2, v_v_1617_);
lean_ctor_set(v___x_1614_, 1, v_k_1616_);
lean_ctor_set(v___x_1614_, 0, v___x_1620_);
v___x_1622_ = v___x_1614_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_k_1616_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_v_1617_);
lean_ctor_set(v_reuseFailAlloc_1626_, 3, v_tree_1541_);
lean_ctor_set(v_reuseFailAlloc_1626_, 4, v_l_1533_);
v___x_1622_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1624_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v_r_1534_);
lean_ctor_set(v___x_1538_, 3, v___x_1622_);
lean_ctor_set(v___x_1538_, 2, v_v_1532_);
lean_ctor_set(v___x_1538_, 1, v_k_1531_);
lean_ctor_set(v___x_1538_, 0, v___x_1619_);
v___x_1624_ = v___x_1538_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1625_, 3, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1625_, 4, v_r_1534_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
else
{
lean_object* v_k_1627_; lean_object* v_v_1628_; lean_object* v_k_1629_; lean_object* v_v_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_size_1530_);
v_k_1627_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_k_1627_);
v_v_1628_ = lean_ctor_get(v___x_1540_, 1);
lean_inc(v_v_1628_);
lean_dec_ref(v___x_1540_);
v_k_1629_ = lean_ctor_get(v_l_1533_, 1);
v_v_1630_ = lean_ctor_get(v_l_1533_, 2);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_l_1533_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; lean_object* v_unused_1646_; lean_object* v_unused_1647_; 
v_unused_1645_ = lean_ctor_get(v_l_1533_, 4);
lean_dec(v_unused_1645_);
v_unused_1646_ = lean_ctor_get(v_l_1533_, 3);
lean_dec(v_unused_1646_);
v_unused_1647_ = lean_ctor_get(v_l_1533_, 0);
lean_dec(v_unused_1647_);
v___x_1632_ = v_l_1533_;
v_isShared_1633_ = v_isSharedCheck_1644_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_v_1630_);
lean_inc(v_k_1629_);
lean_dec(v_l_1533_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1644_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = lean_unsigned_to_nat(3u);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 4, v_r_1534_);
lean_ctor_set(v___x_1632_, 3, v_r_1534_);
lean_ctor_set(v___x_1632_, 2, v_v_1628_);
lean_ctor_set(v___x_1632_, 1, v_k_1627_);
lean_ctor_set(v___x_1632_, 0, v___x_1535_);
v___x_1636_ = v___x_1632_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_k_1627_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_v_1628_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v_r_1534_);
v___x_1636_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 3, v_r_1534_);
lean_ctor_set(v___x_1614_, 0, v___x_1535_);
v___x_1638_ = v___x_1614_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1642_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1642_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1642_, 4, v_r_1534_);
v___x_1638_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1640_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v___x_1638_);
lean_ctor_set(v___x_1538_, 3, v___x_1636_);
lean_ctor_set(v___x_1538_, 2, v_v_1630_);
lean_ctor_set(v___x_1538_, 1, v_k_1629_);
lean_ctor_set(v___x_1538_, 0, v___x_1634_);
v___x_1640_ = v___x_1538_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_k_1629_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_v_1630_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1534_) == 0)
{
lean_object* v_k_1648_; lean_object* v_v_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
lean_dec(v_size_1530_);
v_k_1648_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_k_1648_);
v_v_1649_ = lean_ctor_get(v___x_1540_, 1);
lean_inc(v_v_1649_);
lean_dec_ref(v___x_1540_);
v___x_1650_ = lean_unsigned_to_nat(3u);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 4, v_l_1533_);
lean_ctor_set(v___x_1614_, 2, v_v_1649_);
lean_ctor_set(v___x_1614_, 1, v_k_1648_);
lean_ctor_set(v___x_1614_, 0, v___x_1535_);
v___x_1652_ = v___x_1614_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_k_1648_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_v_1649_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v_l_1533_);
v___x_1652_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1654_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v_r_1534_);
lean_ctor_set(v___x_1538_, 3, v___x_1652_);
lean_ctor_set(v___x_1538_, 2, v_v_1532_);
lean_ctor_set(v___x_1538_, 1, v_k_1531_);
lean_ctor_set(v___x_1538_, 0, v___x_1650_);
v___x_1654_ = v___x_1538_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_r_1534_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
else
{
lean_object* v_k_1657_; lean_object* v_v_1658_; lean_object* v___x_1660_; 
v_k_1657_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_k_1657_);
v_v_1658_ = lean_ctor_get(v___x_1540_, 1);
lean_inc(v_v_1658_);
lean_dec_ref(v___x_1540_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 3, v_r_1534_);
v___x_1660_ = v___x_1614_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_size_1530_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_r_1534_);
v___x_1660_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_unsigned_to_nat(2u);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v___x_1660_);
lean_ctor_set(v___x_1538_, 3, v_r_1534_);
lean_ctor_set(v___x_1538_, 2, v_v_1658_);
lean_ctor_set(v___x_1538_, 1, v_k_1657_);
lean_ctor_set(v___x_1538_, 0, v___x_1661_);
v___x_1663_ = v___x_1538_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_k_1657_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_v_1658_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v___x_1660_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
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
lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1830_; 
lean_inc(v_r_1534_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_r_1346_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; lean_object* v_unused_1832_; lean_object* v_unused_1833_; lean_object* v_unused_1834_; lean_object* v_unused_1835_; 
v_unused_1831_ = lean_ctor_get(v_r_1346_, 4);
lean_dec(v_unused_1831_);
v_unused_1832_ = lean_ctor_get(v_r_1346_, 3);
lean_dec(v_unused_1832_);
v_unused_1833_ = lean_ctor_get(v_r_1346_, 2);
lean_dec(v_unused_1833_);
v_unused_1834_ = lean_ctor_get(v_r_1346_, 1);
lean_dec(v_unused_1834_);
v_unused_1835_ = lean_ctor_get(v_r_1346_, 0);
lean_dec(v_unused_1835_);
v___x_1679_ = v_r_1346_;
v_isShared_1680_ = v_isSharedCheck_1830_;
goto v_resetjp_1678_;
}
else
{
lean_dec(v_r_1346_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1830_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v_tree_1682_; 
v___x_1681_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1531_, v_v_1532_, v_l_1533_, v_r_1534_);
v_tree_1682_ = lean_ctor_get(v___x_1681_, 2);
lean_inc(v_tree_1682_);
if (lean_obj_tag(v_tree_1682_) == 0)
{
lean_object* v_k_1683_; lean_object* v_v_1684_; lean_object* v_size_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_k_1683_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_k_1683_);
v_v_1684_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_v_1684_);
lean_dec_ref(v___x_1681_);
v_size_1685_ = lean_ctor_get(v_tree_1682_, 0);
v___x_1686_ = lean_unsigned_to_nat(3u);
v___x_1687_ = lean_nat_mul(v___x_1686_, v_size_1685_);
v___x_1688_ = lean_nat_dec_lt(v___x_1687_, v_size_1525_);
lean_dec(v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
lean_dec(v_r_1529_);
v___x_1689_ = lean_nat_add(v___x_1535_, v_size_1525_);
v___x_1690_ = lean_nat_add(v___x_1689_, v_size_1685_);
lean_dec(v___x_1689_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 4, v_tree_1682_);
lean_ctor_set(v___x_1679_, 3, v_l_1345_);
lean_ctor_set(v___x_1679_, 2, v_v_1684_);
lean_ctor_set(v___x_1679_, 1, v_k_1683_);
lean_ctor_set(v___x_1679_, 0, v___x_1690_);
v___x_1692_ = v___x_1679_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_k_1683_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_v_1684_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_l_1345_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_tree_1682_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
else
{
lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1759_; 
lean_inc(v_l_1528_);
lean_inc(v_v_1527_);
lean_inc(v_k_1526_);
lean_inc(v_size_1525_);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_l_1345_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; lean_object* v_unused_1761_; lean_object* v_unused_1762_; lean_object* v_unused_1763_; lean_object* v_unused_1764_; 
v_unused_1760_ = lean_ctor_get(v_l_1345_, 4);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v_l_1345_, 3);
lean_dec(v_unused_1761_);
v_unused_1762_ = lean_ctor_get(v_l_1345_, 2);
lean_dec(v_unused_1762_);
v_unused_1763_ = lean_ctor_get(v_l_1345_, 1);
lean_dec(v_unused_1763_);
v_unused_1764_ = lean_ctor_get(v_l_1345_, 0);
lean_dec(v_unused_1764_);
v___x_1695_ = v_l_1345_;
v_isShared_1696_ = v_isSharedCheck_1759_;
goto v_resetjp_1694_;
}
else
{
lean_dec(v_l_1345_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1759_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_size_1697_; lean_object* v_size_1698_; lean_object* v_k_1699_; lean_object* v_v_1700_; lean_object* v_l_1701_; lean_object* v_r_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_size_1697_ = lean_ctor_get(v_l_1528_, 0);
v_size_1698_ = lean_ctor_get(v_r_1529_, 0);
v_k_1699_ = lean_ctor_get(v_r_1529_, 1);
v_v_1700_ = lean_ctor_get(v_r_1529_, 2);
v_l_1701_ = lean_ctor_get(v_r_1529_, 3);
v_r_1702_ = lean_ctor_get(v_r_1529_, 4);
v___x_1703_ = lean_unsigned_to_nat(2u);
v___x_1704_ = lean_nat_mul(v___x_1703_, v_size_1697_);
v___x_1705_ = lean_nat_dec_lt(v_size_1698_, v___x_1704_);
lean_dec(v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1743_; 
lean_inc(v_r_1702_);
lean_inc(v_l_1701_);
lean_inc(v_v_1700_);
lean_inc(v_k_1699_);
lean_del_object(v___x_1695_);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_r_1529_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; lean_object* v_unused_1745_; lean_object* v_unused_1746_; lean_object* v_unused_1747_; lean_object* v_unused_1748_; 
v_unused_1744_ = lean_ctor_get(v_r_1529_, 4);
lean_dec(v_unused_1744_);
v_unused_1745_ = lean_ctor_get(v_r_1529_, 3);
lean_dec(v_unused_1745_);
v_unused_1746_ = lean_ctor_get(v_r_1529_, 2);
lean_dec(v_unused_1746_);
v_unused_1747_ = lean_ctor_get(v_r_1529_, 1);
lean_dec(v_unused_1747_);
v_unused_1748_ = lean_ctor_get(v_r_1529_, 0);
lean_dec(v_unused_1748_);
v___x_1707_ = v_r_1529_;
v_isShared_1708_ = v_isSharedCheck_1743_;
goto v_resetjp_1706_;
}
else
{
lean_dec(v_r_1529_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1743_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___x_1731_; lean_object* v___y_1733_; 
v___x_1709_ = lean_nat_add(v___x_1535_, v_size_1525_);
lean_dec(v_size_1525_);
v___x_1710_ = lean_nat_add(v___x_1709_, v_size_1685_);
lean_dec(v___x_1709_);
v___x_1731_ = lean_nat_add(v___x_1535_, v_size_1697_);
if (lean_obj_tag(v_l_1701_) == 0)
{
lean_object* v_size_1741_; 
v_size_1741_ = lean_ctor_get(v_l_1701_, 0);
lean_inc(v_size_1741_);
v___y_1733_ = v_size_1741_;
goto v___jp_1732_;
}
else
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_unsigned_to_nat(0u);
v___y_1733_ = v___x_1742_;
goto v___jp_1732_;
}
v___jp_1711_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = lean_nat_add(v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec(v___y_1713_);
lean_inc_ref(v_tree_1682_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 4, v_tree_1682_);
lean_ctor_set(v___x_1707_, 3, v_r_1702_);
lean_ctor_set(v___x_1707_, 2, v_v_1684_);
lean_ctor_set(v___x_1707_, 1, v_k_1683_);
lean_ctor_set(v___x_1707_, 0, v___x_1715_);
v___x_1717_ = v___x_1707_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_k_1683_);
lean_ctor_set(v_reuseFailAlloc_1730_, 2, v_v_1684_);
lean_ctor_set(v_reuseFailAlloc_1730_, 3, v_r_1702_);
lean_ctor_set(v_reuseFailAlloc_1730_, 4, v_tree_1682_);
v___x_1717_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_isSharedCheck_1724_ = !lean_is_exclusive(v_tree_1682_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; lean_object* v_unused_1726_; lean_object* v_unused_1727_; lean_object* v_unused_1728_; lean_object* v_unused_1729_; 
v_unused_1725_ = lean_ctor_get(v_tree_1682_, 4);
lean_dec(v_unused_1725_);
v_unused_1726_ = lean_ctor_get(v_tree_1682_, 3);
lean_dec(v_unused_1726_);
v_unused_1727_ = lean_ctor_get(v_tree_1682_, 2);
lean_dec(v_unused_1727_);
v_unused_1728_ = lean_ctor_get(v_tree_1682_, 1);
lean_dec(v_unused_1728_);
v_unused_1729_ = lean_ctor_get(v_tree_1682_, 0);
lean_dec(v_unused_1729_);
v___x_1719_ = v_tree_1682_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_dec(v_tree_1682_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 4, v___x_1717_);
lean_ctor_set(v___x_1719_, 3, v___y_1712_);
lean_ctor_set(v___x_1719_, 2, v_v_1700_);
lean_ctor_set(v___x_1719_, 1, v_k_1699_);
lean_ctor_set(v___x_1719_, 0, v___x_1710_);
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_k_1699_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_v_1700_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v___y_1712_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v___x_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
v___jp_1732_:
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1734_ = lean_nat_add(v___x_1731_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec(v___x_1731_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 4, v_l_1701_);
lean_ctor_set(v___x_1679_, 3, v_l_1528_);
lean_ctor_set(v___x_1679_, 2, v_v_1527_);
lean_ctor_set(v___x_1679_, 1, v_k_1526_);
lean_ctor_set(v___x_1679_, 0, v___x_1734_);
v___x_1736_ = v___x_1679_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_k_1526_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_v_1527_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_l_1528_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_l_1701_);
v___x_1736_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_nat_add(v___x_1535_, v_size_1685_);
if (lean_obj_tag(v_r_1702_) == 0)
{
lean_object* v_size_1738_; 
v_size_1738_ = lean_ctor_get(v_r_1702_, 0);
lean_inc(v_size_1738_);
v___y_1712_ = v___x_1736_;
v___y_1713_ = v___x_1737_;
v___y_1714_ = v_size_1738_;
goto v___jp_1711_;
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_unsigned_to_nat(0u);
v___y_1712_ = v___x_1736_;
v___y_1713_ = v___x_1737_;
v___y_1714_ = v___x_1739_;
goto v___jp_1711_;
}
}
}
}
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1749_ = lean_nat_add(v___x_1535_, v_size_1525_);
lean_dec(v_size_1525_);
v___x_1750_ = lean_nat_add(v___x_1749_, v_size_1685_);
lean_dec(v___x_1749_);
v___x_1751_ = lean_nat_add(v___x_1535_, v_size_1685_);
v___x_1752_ = lean_nat_add(v___x_1751_, v_size_1698_);
lean_dec(v___x_1751_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 4, v_tree_1682_);
lean_ctor_set(v___x_1679_, 3, v_r_1529_);
lean_ctor_set(v___x_1679_, 2, v_v_1684_);
lean_ctor_set(v___x_1679_, 1, v_k_1683_);
lean_ctor_set(v___x_1679_, 0, v___x_1752_);
v___x_1754_ = v___x_1679_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_k_1683_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_v_1684_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_r_1529_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_tree_1682_);
v___x_1754_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1756_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 4, v___x_1754_);
lean_ctor_set(v___x_1695_, 0, v___x_1750_);
v___x_1756_ = v___x_1695_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_k_1526_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_v_1527_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v_l_1528_);
lean_ctor_set(v_reuseFailAlloc_1757_, 4, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1528_) == 0)
{
lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1788_; 
lean_inc_ref(v_l_1528_);
lean_inc(v_v_1527_);
lean_inc(v_k_1526_);
lean_inc(v_size_1525_);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_l_1345_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; lean_object* v_unused_1790_; lean_object* v_unused_1791_; lean_object* v_unused_1792_; lean_object* v_unused_1793_; 
v_unused_1789_ = lean_ctor_get(v_l_1345_, 4);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v_l_1345_, 3);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v_l_1345_, 2);
lean_dec(v_unused_1791_);
v_unused_1792_ = lean_ctor_get(v_l_1345_, 1);
lean_dec(v_unused_1792_);
v_unused_1793_ = lean_ctor_get(v_l_1345_, 0);
lean_dec(v_unused_1793_);
v___x_1766_ = v_l_1345_;
v_isShared_1767_ = v_isSharedCheck_1788_;
goto v_resetjp_1765_;
}
else
{
lean_dec(v_l_1345_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1788_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
if (lean_obj_tag(v_r_1529_) == 0)
{
lean_object* v_k_1768_; lean_object* v_v_1769_; lean_object* v_size_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v_k_1768_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_k_1768_);
v_v_1769_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_v_1769_);
lean_dec_ref(v___x_1681_);
v_size_1770_ = lean_ctor_get(v_r_1529_, 0);
v___x_1771_ = lean_nat_add(v___x_1535_, v_size_1525_);
lean_dec(v_size_1525_);
v___x_1772_ = lean_nat_add(v___x_1535_, v_size_1770_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 4, v_tree_1682_);
lean_ctor_set(v___x_1679_, 3, v_r_1529_);
lean_ctor_set(v___x_1679_, 2, v_v_1769_);
lean_ctor_set(v___x_1679_, 1, v_k_1768_);
lean_ctor_set(v___x_1679_, 0, v___x_1772_);
v___x_1774_ = v___x_1679_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_k_1768_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_v_1769_);
lean_ctor_set(v_reuseFailAlloc_1778_, 3, v_r_1529_);
lean_ctor_set(v_reuseFailAlloc_1778_, 4, v_tree_1682_);
v___x_1774_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1776_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 4, v___x_1774_);
lean_ctor_set(v___x_1766_, 0, v___x_1771_);
v___x_1776_ = v___x_1766_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_k_1526_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_v_1527_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v_l_1528_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
else
{
lean_object* v_k_1779_; lean_object* v_v_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
lean_dec(v_size_1525_);
v_k_1779_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_k_1779_);
v_v_1780_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_v_1780_);
lean_dec_ref(v___x_1681_);
v___x_1781_ = lean_unsigned_to_nat(3u);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 4, v_r_1529_);
lean_ctor_set(v___x_1679_, 3, v_r_1529_);
lean_ctor_set(v___x_1679_, 2, v_v_1780_);
lean_ctor_set(v___x_1679_, 1, v_k_1779_);
lean_ctor_set(v___x_1679_, 0, v___x_1535_);
v___x_1783_ = v___x_1679_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_k_1779_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v_v_1780_);
lean_ctor_set(v_reuseFailAlloc_1787_, 3, v_r_1529_);
lean_ctor_set(v_reuseFailAlloc_1787_, 4, v_r_1529_);
v___x_1783_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1785_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 4, v___x_1783_);
lean_ctor_set(v___x_1766_, 0, v___x_1781_);
v___x_1785_ = v___x_1766_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_k_1526_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_v_1527_);
lean_ctor_set(v_reuseFailAlloc_1786_, 3, v_l_1528_);
lean_ctor_set(v_reuseFailAlloc_1786_, 4, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1529_) == 0)
{
lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1818_; 
lean_inc(v_l_1528_);
lean_inc(v_v_1527_);
lean_inc(v_k_1526_);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_l_1345_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; lean_object* v_unused_1820_; lean_object* v_unused_1821_; lean_object* v_unused_1822_; lean_object* v_unused_1823_; 
v_unused_1819_ = lean_ctor_get(v_l_1345_, 4);
lean_dec(v_unused_1819_);
v_unused_1820_ = lean_ctor_get(v_l_1345_, 3);
lean_dec(v_unused_1820_);
v_unused_1821_ = lean_ctor_get(v_l_1345_, 2);
lean_dec(v_unused_1821_);
v_unused_1822_ = lean_ctor_get(v_l_1345_, 1);
lean_dec(v_unused_1822_);
v_unused_1823_ = lean_ctor_get(v_l_1345_, 0);
lean_dec(v_unused_1823_);
v___x_1795_ = v_l_1345_;
v_isShared_1796_ = v_isSharedCheck_1818_;
goto v_resetjp_1794_;
}
else
{
lean_dec(v_l_1345_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1818_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v_k_1797_; lean_object* v_v_1798_; lean_object* v_k_1799_; lean_object* v_v_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1814_; 
v_k_1797_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_k_1797_);
v_v_1798_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_v_1798_);
lean_dec_ref(v___x_1681_);
v_k_1799_ = lean_ctor_get(v_r_1529_, 1);
v_v_1800_ = lean_ctor_get(v_r_1529_, 2);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_r_1529_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; lean_object* v_unused_1816_; lean_object* v_unused_1817_; 
v_unused_1815_ = lean_ctor_get(v_r_1529_, 4);
lean_dec(v_unused_1815_);
v_unused_1816_ = lean_ctor_get(v_r_1529_, 3);
lean_dec(v_unused_1816_);
v_unused_1817_ = lean_ctor_get(v_r_1529_, 0);
lean_dec(v_unused_1817_);
v___x_1802_ = v_r_1529_;
v_isShared_1803_ = v_isSharedCheck_1814_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_v_1800_);
lean_inc(v_k_1799_);
lean_dec(v_r_1529_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1814_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = lean_unsigned_to_nat(3u);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 4, v_l_1528_);
lean_ctor_set(v___x_1802_, 3, v_l_1528_);
lean_ctor_set(v___x_1802_, 2, v_v_1527_);
lean_ctor_set(v___x_1802_, 1, v_k_1526_);
lean_ctor_set(v___x_1802_, 0, v___x_1535_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_k_1526_);
lean_ctor_set(v_reuseFailAlloc_1813_, 2, v_v_1527_);
lean_ctor_set(v_reuseFailAlloc_1813_, 3, v_l_1528_);
lean_ctor_set(v_reuseFailAlloc_1813_, 4, v_l_1528_);
v___x_1806_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1808_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 4, v_l_1528_);
lean_ctor_set(v___x_1679_, 3, v_l_1528_);
lean_ctor_set(v___x_1679_, 2, v_v_1798_);
lean_ctor_set(v___x_1679_, 1, v_k_1797_);
lean_ctor_set(v___x_1679_, 0, v___x_1535_);
v___x_1808_ = v___x_1679_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_k_1797_);
lean_ctor_set(v_reuseFailAlloc_1812_, 2, v_v_1798_);
lean_ctor_set(v_reuseFailAlloc_1812_, 3, v_l_1528_);
lean_ctor_set(v_reuseFailAlloc_1812_, 4, v_l_1528_);
v___x_1808_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 4, v___x_1808_);
lean_ctor_set(v___x_1795_, 3, v___x_1806_);
lean_ctor_set(v___x_1795_, 2, v_v_1800_);
lean_ctor_set(v___x_1795_, 1, v_k_1799_);
lean_ctor_set(v___x_1795_, 0, v___x_1804_);
v___x_1810_ = v___x_1795_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_k_1799_);
lean_ctor_set(v_reuseFailAlloc_1811_, 2, v_v_1800_);
lean_ctor_set(v_reuseFailAlloc_1811_, 3, v___x_1806_);
lean_ctor_set(v_reuseFailAlloc_1811_, 4, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
}
else
{
lean_object* v_k_1824_; lean_object* v_v_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v_k_1824_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_k_1824_);
v_v_1825_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_v_1825_);
lean_dec_ref(v___x_1681_);
v___x_1826_ = lean_unsigned_to_nat(2u);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 4, v_r_1529_);
lean_ctor_set(v___x_1679_, 3, v_l_1345_);
lean_ctor_set(v___x_1679_, 2, v_v_1825_);
lean_ctor_set(v___x_1679_, 1, v_k_1824_);
lean_ctor_set(v___x_1679_, 0, v___x_1826_);
v___x_1828_ = v___x_1679_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_k_1824_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_v_1825_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_l_1345_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_r_1529_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
}
}
else
{
return v_l_1345_;
}
}
else
{
return v_r_1346_;
}
}
default: 
{
lean_object* v_impl_1836_; lean_object* v___x_1837_; 
v_impl_1836_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_1341_, v_r_1346_);
v___x_1837_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1836_) == 0)
{
if (lean_obj_tag(v_l_1345_) == 0)
{
lean_object* v_size_1838_; lean_object* v_size_1839_; lean_object* v_k_1840_; lean_object* v_v_1841_; lean_object* v_l_1842_; lean_object* v_r_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v_size_1838_ = lean_ctor_get(v_impl_1836_, 0);
lean_inc(v_size_1838_);
v_size_1839_ = lean_ctor_get(v_l_1345_, 0);
v_k_1840_ = lean_ctor_get(v_l_1345_, 1);
v_v_1841_ = lean_ctor_get(v_l_1345_, 2);
v_l_1842_ = lean_ctor_get(v_l_1345_, 3);
v_r_1843_ = lean_ctor_get(v_l_1345_, 4);
lean_inc(v_r_1843_);
v___x_1844_ = lean_unsigned_to_nat(3u);
v___x_1845_ = lean_nat_mul(v___x_1844_, v_size_1838_);
v___x_1846_ = lean_nat_dec_lt(v___x_1845_, v_size_1839_);
lean_dec(v___x_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
lean_dec(v_r_1843_);
v___x_1847_ = lean_nat_add(v___x_1837_, v_size_1839_);
v___x_1848_ = lean_nat_add(v___x_1847_, v_size_1838_);
lean_dec(v_size_1838_);
lean_dec(v___x_1847_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v_impl_1836_);
lean_ctor_set(v___x_1348_, 0, v___x_1848_);
v___x_1850_ = v___x_1348_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1851_, 3, v_l_1345_);
lean_ctor_set(v_reuseFailAlloc_1851_, 4, v_impl_1836_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
else
{
lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1917_; 
lean_inc(v_l_1842_);
lean_inc(v_v_1841_);
lean_inc(v_k_1840_);
lean_inc(v_size_1839_);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_l_1345_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; lean_object* v_unused_1919_; lean_object* v_unused_1920_; lean_object* v_unused_1921_; lean_object* v_unused_1922_; 
v_unused_1918_ = lean_ctor_get(v_l_1345_, 4);
lean_dec(v_unused_1918_);
v_unused_1919_ = lean_ctor_get(v_l_1345_, 3);
lean_dec(v_unused_1919_);
v_unused_1920_ = lean_ctor_get(v_l_1345_, 2);
lean_dec(v_unused_1920_);
v_unused_1921_ = lean_ctor_get(v_l_1345_, 1);
lean_dec(v_unused_1921_);
v_unused_1922_ = lean_ctor_get(v_l_1345_, 0);
lean_dec(v_unused_1922_);
v___x_1853_ = v_l_1345_;
v_isShared_1854_ = v_isSharedCheck_1917_;
goto v_resetjp_1852_;
}
else
{
lean_dec(v_l_1345_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1917_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_size_1855_; lean_object* v_size_1856_; lean_object* v_k_1857_; lean_object* v_v_1858_; lean_object* v_l_1859_; lean_object* v_r_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_size_1855_ = lean_ctor_get(v_l_1842_, 0);
v_size_1856_ = lean_ctor_get(v_r_1843_, 0);
v_k_1857_ = lean_ctor_get(v_r_1843_, 1);
v_v_1858_ = lean_ctor_get(v_r_1843_, 2);
v_l_1859_ = lean_ctor_get(v_r_1843_, 3);
v_r_1860_ = lean_ctor_get(v_r_1843_, 4);
v___x_1861_ = lean_unsigned_to_nat(2u);
v___x_1862_ = lean_nat_mul(v___x_1861_, v_size_1855_);
v___x_1863_ = lean_nat_dec_lt(v_size_1856_, v___x_1862_);
lean_dec(v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1892_; 
lean_inc(v_r_1860_);
lean_inc(v_l_1859_);
lean_inc(v_v_1858_);
lean_inc(v_k_1857_);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_r_1843_);
if (v_isSharedCheck_1892_ == 0)
{
lean_object* v_unused_1893_; lean_object* v_unused_1894_; lean_object* v_unused_1895_; lean_object* v_unused_1896_; lean_object* v_unused_1897_; 
v_unused_1893_ = lean_ctor_get(v_r_1843_, 4);
lean_dec(v_unused_1893_);
v_unused_1894_ = lean_ctor_get(v_r_1843_, 3);
lean_dec(v_unused_1894_);
v_unused_1895_ = lean_ctor_get(v_r_1843_, 2);
lean_dec(v_unused_1895_);
v_unused_1896_ = lean_ctor_get(v_r_1843_, 1);
lean_dec(v_unused_1896_);
v_unused_1897_ = lean_ctor_get(v_r_1843_, 0);
lean_dec(v_unused_1897_);
v___x_1865_ = v_r_1843_;
v_isShared_1866_ = v_isSharedCheck_1892_;
goto v_resetjp_1864_;
}
else
{
lean_dec(v_r_1843_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1892_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___x_1880_; lean_object* v___y_1882_; 
v___x_1867_ = lean_nat_add(v___x_1837_, v_size_1839_);
lean_dec(v_size_1839_);
v___x_1868_ = lean_nat_add(v___x_1867_, v_size_1838_);
lean_dec(v___x_1867_);
v___x_1880_ = lean_nat_add(v___x_1837_, v_size_1855_);
if (lean_obj_tag(v_l_1859_) == 0)
{
lean_object* v_size_1890_; 
v_size_1890_ = lean_ctor_get(v_l_1859_, 0);
lean_inc(v_size_1890_);
v___y_1882_ = v_size_1890_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_unsigned_to_nat(0u);
v___y_1882_ = v___x_1891_;
goto v___jp_1881_;
}
v___jp_1869_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = lean_nat_add(v___y_1870_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec(v___y_1870_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 4, v_impl_1836_);
lean_ctor_set(v___x_1865_, 3, v_r_1860_);
lean_ctor_set(v___x_1865_, 2, v_v_1344_);
lean_ctor_set(v___x_1865_, 1, v_k_1343_);
lean_ctor_set(v___x_1865_, 0, v___x_1873_);
v___x_1875_ = v___x_1865_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1879_, 3, v_r_1860_);
lean_ctor_set(v_reuseFailAlloc_1879_, 4, v_impl_1836_);
v___x_1875_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 4, v___x_1875_);
lean_ctor_set(v___x_1853_, 3, v___y_1871_);
lean_ctor_set(v___x_1853_, 2, v_v_1858_);
lean_ctor_set(v___x_1853_, 1, v_k_1857_);
lean_ctor_set(v___x_1853_, 0, v___x_1868_);
v___x_1877_ = v___x_1853_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_k_1857_);
lean_ctor_set(v_reuseFailAlloc_1878_, 2, v_v_1858_);
lean_ctor_set(v_reuseFailAlloc_1878_, 3, v___y_1871_);
lean_ctor_set(v_reuseFailAlloc_1878_, 4, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
v___jp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = lean_nat_add(v___x_1880_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec(v___x_1880_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v_l_1859_);
lean_ctor_set(v___x_1348_, 3, v_l_1842_);
lean_ctor_set(v___x_1348_, 2, v_v_1841_);
lean_ctor_set(v___x_1348_, 1, v_k_1840_);
lean_ctor_set(v___x_1348_, 0, v___x_1883_);
v___x_1885_ = v___x_1348_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_k_1840_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_v_1841_);
lean_ctor_set(v_reuseFailAlloc_1889_, 3, v_l_1842_);
lean_ctor_set(v_reuseFailAlloc_1889_, 4, v_l_1859_);
v___x_1885_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_nat_add(v___x_1837_, v_size_1838_);
lean_dec(v_size_1838_);
if (lean_obj_tag(v_r_1860_) == 0)
{
lean_object* v_size_1887_; 
v_size_1887_ = lean_ctor_get(v_r_1860_, 0);
lean_inc(v_size_1887_);
v___y_1870_ = v___x_1886_;
v___y_1871_ = v___x_1885_;
v___y_1872_ = v_size_1887_;
goto v___jp_1869_;
}
else
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_unsigned_to_nat(0u);
v___y_1870_ = v___x_1886_;
v___y_1871_ = v___x_1885_;
v___y_1872_ = v___x_1888_;
goto v___jp_1869_;
}
}
}
}
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
lean_del_object(v___x_1348_);
v___x_1898_ = lean_nat_add(v___x_1837_, v_size_1839_);
lean_dec(v_size_1839_);
v___x_1899_ = lean_nat_add(v___x_1898_, v_size_1838_);
lean_dec(v___x_1898_);
v___x_1900_ = lean_nat_add(v___x_1837_, v_size_1838_);
lean_dec(v_size_1838_);
v___x_1901_ = lean_nat_add(v___x_1900_, v_size_1856_);
lean_dec(v___x_1900_);
lean_inc_ref(v_impl_1836_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 4, v_impl_1836_);
lean_ctor_set(v___x_1853_, 3, v_r_1843_);
lean_ctor_set(v___x_1853_, 2, v_v_1344_);
lean_ctor_set(v___x_1853_, 1, v_k_1343_);
lean_ctor_set(v___x_1853_, 0, v___x_1901_);
v___x_1903_ = v___x_1853_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1916_, 3, v_r_1843_);
lean_ctor_set(v_reuseFailAlloc_1916_, 4, v_impl_1836_);
v___x_1903_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
v_isSharedCheck_1910_ = !lean_is_exclusive(v_impl_1836_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; lean_object* v_unused_1912_; lean_object* v_unused_1913_; lean_object* v_unused_1914_; lean_object* v_unused_1915_; 
v_unused_1911_ = lean_ctor_get(v_impl_1836_, 4);
lean_dec(v_unused_1911_);
v_unused_1912_ = lean_ctor_get(v_impl_1836_, 3);
lean_dec(v_unused_1912_);
v_unused_1913_ = lean_ctor_get(v_impl_1836_, 2);
lean_dec(v_unused_1913_);
v_unused_1914_ = lean_ctor_get(v_impl_1836_, 1);
lean_dec(v_unused_1914_);
v_unused_1915_ = lean_ctor_get(v_impl_1836_, 0);
lean_dec(v_unused_1915_);
v___x_1905_ = v_impl_1836_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_dec(v_impl_1836_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 4, v___x_1903_);
lean_ctor_set(v___x_1905_, 3, v_l_1842_);
lean_ctor_set(v___x_1905_, 2, v_v_1841_);
lean_ctor_set(v___x_1905_, 1, v_k_1840_);
lean_ctor_set(v___x_1905_, 0, v___x_1899_);
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_k_1840_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v_v_1841_);
lean_ctor_set(v_reuseFailAlloc_1909_, 3, v_l_1842_);
lean_ctor_set(v_reuseFailAlloc_1909_, 4, v___x_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v_size_1923_ = lean_ctor_get(v_impl_1836_, 0);
lean_inc(v_size_1923_);
v___x_1924_ = lean_nat_add(v___x_1837_, v_size_1923_);
lean_dec(v_size_1923_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v_impl_1836_);
lean_ctor_set(v___x_1348_, 0, v___x_1924_);
v___x_1926_ = v___x_1348_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v_l_1345_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v_impl_1836_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
else
{
if (lean_obj_tag(v_l_1345_) == 0)
{
lean_object* v_l_1928_; 
v_l_1928_ = lean_ctor_get(v_l_1345_, 3);
if (lean_obj_tag(v_l_1928_) == 0)
{
lean_object* v_r_1929_; 
lean_inc_ref(v_l_1928_);
v_r_1929_ = lean_ctor_get(v_l_1345_, 4);
lean_inc(v_r_1929_);
if (lean_obj_tag(v_r_1929_) == 0)
{
lean_object* v_size_1930_; lean_object* v_k_1931_; lean_object* v_v_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1945_; 
v_size_1930_ = lean_ctor_get(v_l_1345_, 0);
v_k_1931_ = lean_ctor_get(v_l_1345_, 1);
v_v_1932_ = lean_ctor_get(v_l_1345_, 2);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_l_1345_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; lean_object* v_unused_1947_; 
v_unused_1946_ = lean_ctor_get(v_l_1345_, 4);
lean_dec(v_unused_1946_);
v_unused_1947_ = lean_ctor_get(v_l_1345_, 3);
lean_dec(v_unused_1947_);
v___x_1934_ = v_l_1345_;
v_isShared_1935_ = v_isSharedCheck_1945_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_v_1932_);
lean_inc(v_k_1931_);
lean_inc(v_size_1930_);
lean_dec(v_l_1345_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1945_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_size_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
v_size_1936_ = lean_ctor_get(v_r_1929_, 0);
v___x_1937_ = lean_nat_add(v___x_1837_, v_size_1930_);
lean_dec(v_size_1930_);
v___x_1938_ = lean_nat_add(v___x_1837_, v_size_1936_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 4, v_impl_1836_);
lean_ctor_set(v___x_1934_, 3, v_r_1929_);
lean_ctor_set(v___x_1934_, 2, v_v_1344_);
lean_ctor_set(v___x_1934_, 1, v_k_1343_);
lean_ctor_set(v___x_1934_, 0, v___x_1938_);
v___x_1940_ = v___x_1934_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1944_, 3, v_r_1929_);
lean_ctor_set(v_reuseFailAlloc_1944_, 4, v_impl_1836_);
v___x_1940_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1942_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v___x_1940_);
lean_ctor_set(v___x_1348_, 3, v_l_1928_);
lean_ctor_set(v___x_1348_, 2, v_v_1932_);
lean_ctor_set(v___x_1348_, 1, v_k_1931_);
lean_ctor_set(v___x_1348_, 0, v___x_1937_);
v___x_1942_ = v___x_1348_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_k_1931_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v_v_1932_);
lean_ctor_set(v_reuseFailAlloc_1943_, 3, v_l_1928_);
lean_ctor_set(v_reuseFailAlloc_1943_, 4, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_k_1948_; lean_object* v_v_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1960_; 
v_k_1948_ = lean_ctor_get(v_l_1345_, 1);
v_v_1949_ = lean_ctor_get(v_l_1345_, 2);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_l_1345_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; lean_object* v_unused_1962_; lean_object* v_unused_1963_; 
v_unused_1961_ = lean_ctor_get(v_l_1345_, 4);
lean_dec(v_unused_1961_);
v_unused_1962_ = lean_ctor_get(v_l_1345_, 3);
lean_dec(v_unused_1962_);
v_unused_1963_ = lean_ctor_get(v_l_1345_, 0);
lean_dec(v_unused_1963_);
v___x_1951_ = v_l_1345_;
v_isShared_1952_ = v_isSharedCheck_1960_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_v_1949_);
lean_inc(v_k_1948_);
lean_dec(v_l_1345_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1960_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_unsigned_to_nat(3u);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 3, v_r_1929_);
lean_ctor_set(v___x_1951_, 2, v_v_1344_);
lean_ctor_set(v___x_1951_, 1, v_k_1343_);
lean_ctor_set(v___x_1951_, 0, v___x_1837_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v_r_1929_);
lean_ctor_set(v_reuseFailAlloc_1959_, 4, v_r_1929_);
v___x_1955_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v___x_1955_);
lean_ctor_set(v___x_1348_, 3, v_l_1928_);
lean_ctor_set(v___x_1348_, 2, v_v_1949_);
lean_ctor_set(v___x_1348_, 1, v_k_1948_);
lean_ctor_set(v___x_1348_, 0, v___x_1953_);
v___x_1957_ = v___x_1348_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_k_1948_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v_v_1949_);
lean_ctor_set(v_reuseFailAlloc_1958_, 3, v_l_1928_);
lean_ctor_set(v_reuseFailAlloc_1958_, 4, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
else
{
lean_object* v_r_1964_; 
v_r_1964_ = lean_ctor_get(v_l_1345_, 4);
lean_inc(v_r_1964_);
if (lean_obj_tag(v_r_1964_) == 0)
{
lean_object* v_k_1965_; lean_object* v_v_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1989_; 
lean_inc(v_l_1928_);
v_k_1965_ = lean_ctor_get(v_l_1345_, 1);
v_v_1966_ = lean_ctor_get(v_l_1345_, 2);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_l_1345_);
if (v_isSharedCheck_1989_ == 0)
{
lean_object* v_unused_1990_; lean_object* v_unused_1991_; lean_object* v_unused_1992_; 
v_unused_1990_ = lean_ctor_get(v_l_1345_, 4);
lean_dec(v_unused_1990_);
v_unused_1991_ = lean_ctor_get(v_l_1345_, 3);
lean_dec(v_unused_1991_);
v_unused_1992_ = lean_ctor_get(v_l_1345_, 0);
lean_dec(v_unused_1992_);
v___x_1968_ = v_l_1345_;
v_isShared_1969_ = v_isSharedCheck_1989_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_v_1966_);
lean_inc(v_k_1965_);
lean_dec(v_l_1345_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1989_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_k_1970_; lean_object* v_v_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1985_; 
v_k_1970_ = lean_ctor_get(v_r_1964_, 1);
v_v_1971_ = lean_ctor_get(v_r_1964_, 2);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_r_1964_);
if (v_isSharedCheck_1985_ == 0)
{
lean_object* v_unused_1986_; lean_object* v_unused_1987_; lean_object* v_unused_1988_; 
v_unused_1986_ = lean_ctor_get(v_r_1964_, 4);
lean_dec(v_unused_1986_);
v_unused_1987_ = lean_ctor_get(v_r_1964_, 3);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_r_1964_, 0);
lean_dec(v_unused_1988_);
v___x_1973_ = v_r_1964_;
v_isShared_1974_ = v_isSharedCheck_1985_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_v_1971_);
lean_inc(v_k_1970_);
lean_dec(v_r_1964_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1985_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1975_ = lean_unsigned_to_nat(3u);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 4, v_l_1928_);
lean_ctor_set(v___x_1973_, 3, v_l_1928_);
lean_ctor_set(v___x_1973_, 2, v_v_1966_);
lean_ctor_set(v___x_1973_, 1, v_k_1965_);
lean_ctor_set(v___x_1973_, 0, v___x_1837_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_1984_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_1984_, 3, v_l_1928_);
lean_ctor_set(v_reuseFailAlloc_1984_, 4, v_l_1928_);
v___x_1977_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1979_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v_l_1928_);
lean_ctor_set(v___x_1968_, 2, v_v_1344_);
lean_ctor_set(v___x_1968_, 1, v_k_1343_);
lean_ctor_set(v___x_1968_, 0, v___x_1837_);
v___x_1979_ = v___x_1968_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v_l_1928_);
lean_ctor_set(v_reuseFailAlloc_1983_, 4, v_l_1928_);
v___x_1979_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v___x_1979_);
lean_ctor_set(v___x_1348_, 3, v___x_1977_);
lean_ctor_set(v___x_1348_, 2, v_v_1971_);
lean_ctor_set(v___x_1348_, 1, v_k_1970_);
lean_ctor_set(v___x_1348_, 0, v___x_1975_);
v___x_1981_ = v___x_1348_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_k_1970_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_v_1971_);
lean_ctor_set(v_reuseFailAlloc_1982_, 3, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1982_, 4, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = lean_unsigned_to_nat(2u);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v_r_1964_);
lean_ctor_set(v___x_1348_, 0, v___x_1993_);
v___x_1995_ = v___x_1348_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v_l_1345_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v_r_1964_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
else
{
lean_object* v___x_1998_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v_l_1345_);
lean_ctor_set(v___x_1348_, 0, v___x_1837_);
v___x_1998_ = v___x_1348_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_k_1343_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_v_1344_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_l_1345_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v_l_1345_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
}
}
else
{
return v_t_1342_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg___boxed(lean_object* v_k_2002_, lean_object* v_t_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2002_, v_t_2003_);
lean_dec(v_k_2002_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_2005_, lean_object* v_v_2006_, lean_object* v_i_2007_){
_start:
{
lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2008_ = lean_array_get_size(v_xs_2005_);
v___x_2009_ = lean_nat_dec_lt(v_i_2007_, v___x_2008_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; 
lean_dec(v_i_2007_);
v___x_2010_ = lean_box(0);
return v___x_2010_;
}
else
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = lean_array_fget_borrowed(v_xs_2005_, v_i_2007_);
v___x_2012_ = l_Lean_instBEqFVarId_beq(v___x_2011_, v_v_2006_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_unsigned_to_nat(1u);
v___x_2014_ = lean_nat_add(v_i_2007_, v___x_2013_);
lean_dec(v_i_2007_);
v_i_2007_ = v___x_2014_;
goto _start;
}
else
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_i_2007_);
return v___x_2016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_2017_, lean_object* v_v_2018_, lean_object* v_i_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2017_, v_v_2018_, v_i_2019_);
lean_dec(v_v_2018_);
lean_dec_ref(v_xs_2017_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(lean_object* v_xs_2021_, lean_object* v_v_2022_){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2024_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1_spec__3(v_xs_2021_, v_v_2022_, v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2025_, lean_object* v_v_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_xs_2025_, v_v_2026_);
lean_dec(v_v_2026_);
lean_dec_ref(v_xs_2025_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(lean_object* v_x_2028_, size_t v_x_2029_, lean_object* v_x_2030_){
_start:
{
if (lean_obj_tag(v_x_2028_) == 0)
{
lean_object* v_es_2031_; lean_object* v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; lean_object* v_j_2035_; lean_object* v_entry_2036_; 
v_es_2031_ = lean_ctor_get(v_x_2028_, 0);
v___x_2032_ = lean_box(2);
v___x_2033_ = ((size_t)31ULL);
v___x_2034_ = lean_usize_land(v_x_2029_, v___x_2033_);
v_j_2035_ = lean_usize_to_nat(v___x_2034_);
v_entry_2036_ = lean_array_get(v___x_2032_, v_es_2031_, v_j_2035_);
switch(lean_obj_tag(v_entry_2036_))
{
case 0:
{
lean_object* v_key_2037_; uint8_t v___x_2038_; 
v_key_2037_ = lean_ctor_get(v_entry_2036_, 0);
lean_inc(v_key_2037_);
lean_dec_ref_known(v_entry_2036_, 2);
v___x_2038_ = l_Lean_instBEqFVarId_beq(v_x_2030_, v_key_2037_);
lean_dec(v_key_2037_);
if (v___x_2038_ == 0)
{
lean_dec(v_j_2035_);
return v_x_2028_;
}
else
{
lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2046_; 
lean_inc_ref(v_es_2031_);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_x_2028_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v_x_2028_, 0);
lean_dec(v_unused_2047_);
v___x_2040_ = v_x_2028_;
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v_x_2028_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_array_set(v_es_2031_, v_j_2035_, v___x_2032_);
lean_dec(v_j_2035_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2042_);
v___x_2044_ = v___x_2040_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
case 1:
{
lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2082_; 
lean_inc_ref(v_es_2031_);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_x_2028_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v_x_2028_, 0);
lean_dec(v_unused_2083_);
v___x_2049_ = v_x_2028_;
v_isShared_2050_ = v_isSharedCheck_2082_;
goto v_resetjp_2048_;
}
else
{
lean_dec(v_x_2028_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2082_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_node_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2081_; 
v_node_2051_ = lean_ctor_get(v_entry_2036_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_entry_2036_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2053_ = v_entry_2036_;
v_isShared_2054_ = v_isSharedCheck_2081_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_node_2051_);
lean_dec(v_entry_2036_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2081_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
size_t v___x_2055_; lean_object* v_entries_2056_; size_t v___x_2057_; lean_object* v_newNode_2058_; lean_object* v___x_2059_; 
v___x_2055_ = ((size_t)5ULL);
v_entries_2056_ = lean_array_set(v_es_2031_, v_j_2035_, v___x_2032_);
v___x_2057_ = lean_usize_shift_right(v_x_2029_, v___x_2055_);
v_newNode_2058_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_node_2051_, v___x_2057_, v_x_2030_);
lean_inc_ref(v_newNode_2058_);
v___x_2059_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2058_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v___x_2061_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v_newNode_2058_);
v___x_2061_ = v___x_2053_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_newNode_2058_);
v___x_2061_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2062_ = lean_array_set(v_entries_2056_, v_j_2035_, v___x_2061_);
lean_dec(v_j_2035_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2062_);
v___x_2064_ = v___x_2049_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
lean_object* v_val_2067_; lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2080_; 
lean_dec_ref(v_newNode_2058_);
lean_del_object(v___x_2053_);
v_val_2067_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_val_2067_);
lean_dec_ref_known(v___x_2059_, 1);
v_fst_2068_ = lean_ctor_get(v_val_2067_, 0);
v_snd_2069_ = lean_ctor_get(v_val_2067_, 1);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_val_2067_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2071_ = v_val_2067_;
v_isShared_2072_ = v_isSharedCheck_2080_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_snd_2069_);
lean_inc(v_fst_2068_);
lean_dec(v_val_2067_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2080_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_fst_2068_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_snd_2069_);
v___x_2074_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2075_ = lean_array_set(v_entries_2056_, v_j_2035_, v___x_2074_);
lean_dec(v_j_2035_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2075_);
v___x_2077_ = v___x_2049_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2035_);
return v_x_2028_;
}
}
}
else
{
lean_object* v_ks_2084_; lean_object* v_vs_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2099_; 
v_ks_2084_ = lean_ctor_get(v_x_2028_, 0);
v_vs_2085_ = lean_ctor_get(v_x_2028_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_x_2028_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2087_ = v_x_2028_;
v_isShared_2088_ = v_isSharedCheck_2099_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_vs_2085_);
lean_inc(v_ks_2084_);
lean_dec(v_x_2028_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2099_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0_spec__1(v_ks_2084_, v_x_2030_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v___x_2091_; 
if (v_isShared_2088_ == 0)
{
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_ks_2084_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_vs_2085_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
else
{
lean_object* v_val_2093_; lean_object* v_keys_x27_2094_; lean_object* v_vals_x27_2095_; lean_object* v___x_2097_; 
v_val_2093_ = lean_ctor_get(v___x_2089_, 0);
lean_inc_n(v_val_2093_, 2);
lean_dec_ref_known(v___x_2089_, 1);
v_keys_x27_2094_ = l_Array_eraseIdx___redArg(v_ks_2084_, v_val_2093_);
v_vals_x27_2095_ = l_Array_eraseIdx___redArg(v_vs_2085_, v_val_2093_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v_vals_x27_2095_);
lean_ctor_set(v___x_2087_, 0, v_keys_x27_2094_);
v___x_2097_ = v___x_2087_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_keys_x27_2094_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_vals_x27_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_){
_start:
{
size_t v_x_2633__boxed_2103_; lean_object* v_res_2104_; 
v_x_2633__boxed_2103_ = lean_unbox_usize(v_x_2101_);
lean_dec(v_x_2101_);
v_res_2104_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2100_, v_x_2633__boxed_2103_, v_x_2102_);
lean_dec(v_x_2102_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(lean_object* v_x_2105_, lean_object* v_x_2106_){
_start:
{
uint64_t v___x_2107_; size_t v_h_2108_; lean_object* v___x_2109_; 
v___x_2107_ = l_Lean_instHashableFVarId_hash(v_x_2106_);
v_h_2108_ = lean_uint64_to_usize(v___x_2107_);
v___x_2109_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2105_, v_h_2108_, v_x_2106_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg___boxed(lean_object* v_x_2110_, lean_object* v_x_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2110_, v_x_2111_);
lean_dec(v_x_2111_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* lean_local_ctx_erase(lean_object* v_lctx_2113_, lean_object* v_fvarId_2114_){
_start:
{
lean_object* v_fvarIdToDecl_2115_; lean_object* v_decls_2116_; lean_object* v_auxDeclToFullName_2117_; lean_object* v___x_2118_; 
v_fvarIdToDecl_2115_ = lean_ctor_get(v_lctx_2113_, 0);
v_decls_2116_ = lean_ctor_get(v_lctx_2113_, 1);
v_auxDeclToFullName_2117_ = lean_ctor_get(v_lctx_2113_, 2);
v___x_2118_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_2115_, v_fvarId_2114_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_dec(v_fvarId_2114_);
return v_lctx_2113_;
}
else
{
lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2138_; 
lean_inc(v_auxDeclToFullName_2117_);
lean_inc_ref(v_decls_2116_);
lean_inc_ref(v_fvarIdToDecl_2115_);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_lctx_2113_);
if (v_isSharedCheck_2138_ == 0)
{
lean_object* v_unused_2139_; lean_object* v_unused_2140_; lean_object* v_unused_2141_; 
v_unused_2139_ = lean_ctor_get(v_lctx_2113_, 2);
lean_dec(v_unused_2139_);
v_unused_2140_ = lean_ctor_get(v_lctx_2113_, 1);
lean_dec(v_unused_2140_);
v_unused_2141_ = lean_ctor_get(v_lctx_2113_, 0);
lean_dec(v_unused_2141_);
v___x_2120_ = v_lctx_2113_;
v_isShared_2121_ = v_isSharedCheck_2138_;
goto v_resetjp_2119_;
}
else
{
lean_dec(v_lctx_2113_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2138_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v_val_2122_; lean_object* v___x_2123_; lean_object* v___y_2125_; lean_object* v_index_2137_; 
v_val_2122_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_val_2122_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2123_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2115_, v_fvarId_2114_);
v_index_2137_ = lean_ctor_get(v_val_2122_, 0);
lean_inc(v_index_2137_);
v___y_2125_ = v_index_2137_;
goto v___jp_2124_;
v___jp_2124_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2126_ = lean_box(0);
v___x_2127_ = l_Lean_PersistentArray_set___redArg(v_decls_2116_, v___y_2125_, v___x_2126_);
lean_dec(v___y_2125_);
v___x_2128_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2127_);
v___x_2129_ = l_Lean_LocalDecl_isAuxDecl(v_val_2122_);
lean_dec(v_val_2122_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2131_; 
lean_dec(v_fvarId_2114_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v___x_2128_);
lean_ctor_set(v___x_2120_, 0, v___x_2123_);
v___x_2131_ = v___x_2120_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_auxDeclToFullName_2117_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2133_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_fvarId_2114_, v_auxDeclToFullName_2117_);
lean_dec(v_fvarId_2114_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 2, v___x_2133_);
lean_ctor_set(v___x_2120_, 1, v___x_2128_);
lean_ctor_set(v___x_2120_, 0, v___x_2123_);
v___x_2135_ = v___x_2120_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(lean_object* v_00_u03b2_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_x_2143_, v_x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___boxed(lean_object* v_00_u03b2_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0(v_00_u03b2_2146_, v_x_2147_, v_x_2148_);
lean_dec(v_x_2148_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(lean_object* v_00_u03b2_2150_, lean_object* v_k_2151_, lean_object* v_t_2152_, lean_object* v_h_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v_k_2151_, v_t_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___boxed(lean_object* v_00_u03b2_2155_, lean_object* v_k_2156_, lean_object* v_t_2157_, lean_object* v_h_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1(v_00_u03b2_2155_, v_k_2156_, v_t_2157_, v_h_2158_);
lean_dec(v_k_2156_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(lean_object* v_00_u03b2_2160_, lean_object* v_x_2161_, size_t v_x_2162_, lean_object* v_x_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___redArg(v_x_2161_, v_x_2162_, v_x_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
size_t v_x_2855__boxed_2169_; lean_object* v_res_2170_; 
v_x_2855__boxed_2169_ = lean_unbox_usize(v_x_2167_);
lean_dec(v_x_2167_);
v_res_2170_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0_spec__0(v_00_u03b2_2165_, v_x_2166_, v_x_2855__boxed_2169_, v_x_2168_);
lean_dec(v_x_2168_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_pop(lean_object* v_lctx_2171_){
_start:
{
lean_object* v_decls_2172_; lean_object* v_fvarIdToDecl_2173_; lean_object* v_auxDeclToFullName_2174_; lean_object* v_size_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v_decls_2172_ = lean_ctor_get(v_lctx_2171_, 1);
v_fvarIdToDecl_2173_ = lean_ctor_get(v_lctx_2171_, 0);
v_auxDeclToFullName_2174_ = lean_ctor_get(v_lctx_2171_, 2);
v_size_2175_ = lean_ctor_get(v_decls_2172_, 2);
v___x_2176_ = lean_unsigned_to_nat(0u);
v___x_2177_ = lean_nat_dec_eq(v_size_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_unsigned_to_nat(1u);
v___x_2180_ = lean_nat_sub(v_size_2175_, v___x_2179_);
v___x_2181_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2178_, v_decls_2172_, v___x_2180_);
lean_dec(v___x_2180_);
if (lean_obj_tag(v___x_2181_) == 0)
{
return v_lctx_2171_;
}
else
{
lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2200_; 
lean_inc(v_auxDeclToFullName_2174_);
lean_inc_ref(v_fvarIdToDecl_2173_);
lean_inc_ref(v_decls_2172_);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_lctx_2171_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; lean_object* v_unused_2202_; lean_object* v_unused_2203_; 
v_unused_2201_ = lean_ctor_get(v_lctx_2171_, 2);
lean_dec(v_unused_2201_);
v_unused_2202_ = lean_ctor_get(v_lctx_2171_, 1);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_lctx_2171_, 0);
lean_dec(v_unused_2203_);
v___x_2183_ = v_lctx_2171_;
v_isShared_2184_ = v_isSharedCheck_2200_;
goto v_resetjp_2182_;
}
else
{
lean_dec(v_lctx_2171_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2200_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v_val_2185_; lean_object* v___y_2187_; lean_object* v_fvarId_2199_; 
v_val_2185_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_val_2185_);
lean_dec_ref_known(v___x_2181_, 1);
v_fvarId_2199_ = lean_ctor_get(v_val_2185_, 1);
lean_inc(v_fvarId_2199_);
v___y_2187_ = v_fvarId_2199_;
goto v___jp_2186_;
v___jp_2186_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2188_ = l_Lean_PersistentHashMap_erase___at___00Lean_LocalContext_erase_spec__0___redArg(v_fvarIdToDecl_2173_, v___y_2187_);
v___x_2189_ = l_Lean_PersistentArray_pop___redArg(v_decls_2172_);
v___x_2190_ = l___private_Lean_LocalContext_0__Lean_LocalContext_popTailNoneAux(v___x_2189_);
v___x_2191_ = l_Lean_LocalDecl_isAuxDecl(v_val_2185_);
lean_dec(v_val_2185_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2193_; 
lean_dec(v___y_2187_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 1, v___x_2190_);
lean_ctor_set(v___x_2183_, 0, v___x_2188_);
v___x_2193_ = v___x_2183_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_auxDeclToFullName_2174_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LocalContext_erase_spec__1___redArg(v___y_2187_, v_auxDeclToFullName_2174_);
lean_dec(v___y_2187_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 2, v___x_2195_);
lean_ctor_set(v___x_2183_, 1, v___x_2190_);
lean_ctor_set(v___x_2183_, 0, v___x_2188_);
v___x_2197_ = v___x_2183_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
}
else
{
return v_lctx_2171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(lean_object* v_userName_2204_, lean_object* v_as_2205_, lean_object* v_i_2206_){
_start:
{
lean_object* v_zero_2207_; uint8_t v_isZero_2208_; 
v_zero_2207_ = lean_unsigned_to_nat(0u);
v_isZero_2208_ = lean_nat_dec_eq(v_i_2206_, v_zero_2207_);
if (v_isZero_2208_ == 1)
{
lean_object* v___x_2209_; 
lean_dec(v_i_2206_);
v___x_2209_ = lean_box(0);
return v___x_2209_;
}
else
{
lean_object* v_one_2210_; lean_object* v_n_2211_; lean_object* v___y_2213_; lean_object* v___x_2215_; lean_object* v___y_2217_; 
v_one_2210_ = lean_unsigned_to_nat(1u);
v_n_2211_ = lean_nat_sub(v_i_2206_, v_one_2210_);
lean_dec(v_i_2206_);
v___x_2215_ = lean_array_fget_borrowed(v_as_2205_, v_n_2211_);
if (lean_obj_tag(v___x_2215_) == 0)
{
v___y_2213_ = v___x_2215_;
goto v___jp_2212_;
}
else
{
lean_object* v_val_2220_; lean_object* v_userName_2221_; 
v_val_2220_ = lean_ctor_get(v___x_2215_, 0);
v_userName_2221_ = lean_ctor_get(v_val_2220_, 2);
v___y_2217_ = v_userName_2221_;
goto v___jp_2216_;
}
v___jp_2212_:
{
if (lean_obj_tag(v___y_2213_) == 0)
{
v_i_2206_ = v_n_2211_;
goto _start;
}
else
{
lean_dec(v_n_2211_);
lean_inc_ref(v___y_2213_);
return v___y_2213_;
}
}
v___jp_2216_:
{
uint8_t v___x_2218_; 
v___x_2218_ = lean_name_eq(v___y_2217_, v_userName_2204_);
if (v___x_2218_ == 0)
{
v_i_2206_ = v_n_2211_;
goto _start;
}
else
{
v___y_2213_ = v___x_2215_;
goto v___jp_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_userName_2222_, lean_object* v_as_2223_, lean_object* v_i_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2222_, v_as_2223_, v_i_2224_);
lean_dec_ref(v_as_2223_);
lean_dec(v_userName_2222_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(lean_object* v_userName_2226_, lean_object* v_as_2227_, lean_object* v_i_2228_){
_start:
{
lean_object* v_zero_2229_; uint8_t v_isZero_2230_; 
v_zero_2229_ = lean_unsigned_to_nat(0u);
v_isZero_2230_ = lean_nat_dec_eq(v_i_2228_, v_zero_2229_);
if (v_isZero_2230_ == 1)
{
lean_object* v___x_2231_; 
lean_dec(v_i_2228_);
v___x_2231_ = lean_box(0);
return v___x_2231_;
}
else
{
lean_object* v_one_2232_; lean_object* v_n_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_one_2232_ = lean_unsigned_to_nat(1u);
v_n_2233_ = lean_nat_sub(v_i_2228_, v_one_2232_);
lean_dec(v_i_2228_);
v___x_2234_ = lean_array_fget_borrowed(v_as_2227_, v_n_2233_);
v___x_2235_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2226_, v___x_2234_);
if (lean_obj_tag(v___x_2235_) == 0)
{
v_i_2228_ = v_n_2233_;
goto _start;
}
else
{
lean_dec(v_n_2233_);
return v___x_2235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(lean_object* v_userName_2237_, lean_object* v_x_2238_){
_start:
{
if (lean_obj_tag(v_x_2238_) == 0)
{
lean_object* v_cs_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_cs_2239_ = lean_ctor_get(v_x_2238_, 0);
v___x_2240_ = lean_array_get_size(v_cs_2239_);
v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2237_, v_cs_2239_, v___x_2240_);
return v___x_2241_;
}
else
{
lean_object* v_vs_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_vs_2242_ = lean_ctor_get(v_x_2238_, 0);
v___x_2243_ = lean_array_get_size(v_vs_2242_);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2237_, v_vs_2242_, v___x_2243_);
return v___x_2244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1___boxed(lean_object* v_userName_2245_, lean_object* v_x_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2245_, v_x_2246_);
lean_dec_ref(v_x_2246_);
lean_dec(v_userName_2245_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_userName_2248_, lean_object* v_as_2249_, lean_object* v_i_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2248_, v_as_2249_, v_i_2250_);
lean_dec_ref(v_as_2249_);
lean_dec(v_userName_2248_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(lean_object* v_userName_2252_, lean_object* v_t_2253_){
_start:
{
lean_object* v_root_2254_; lean_object* v_tail_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v_root_2254_ = lean_ctor_get(v_t_2253_, 0);
v_tail_2255_ = lean_ctor_get(v_t_2253_, 1);
v___x_2256_ = lean_array_get_size(v_tail_2255_);
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2252_, v_tail_2255_, v___x_2256_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v___x_2258_; 
v___x_2258_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1(v_userName_2252_, v_root_2254_);
return v___x_2258_;
}
else
{
return v___x_2257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0___boxed(lean_object* v_userName_2259_, lean_object* v_t_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2259_, v_t_2260_);
lean_dec_ref(v_t_2260_);
lean_dec(v_userName_2259_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object* v_lctx_2262_, lean_object* v_userName_2263_){
_start:
{
lean_object* v_decls_2264_; lean_object* v___x_2265_; 
v_decls_2264_ = lean_ctor_get(v_lctx_2262_, 1);
v___x_2265_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0(v_userName_2263_, v_decls_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserName_x3f___boxed(lean_object* v_lctx_2266_, lean_object* v_userName_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2266_, v_userName_2267_);
lean_dec(v_userName_2267_);
lean_dec_ref(v_lctx_2266_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(lean_object* v_userName_2269_, lean_object* v_as_2270_, lean_object* v_i_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___redArg(v_userName_2269_, v_as_2270_, v_i_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0___boxed(lean_object* v_userName_2274_, lean_object* v_as_2275_, lean_object* v_i_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__0(v_userName_2274_, v_as_2275_, v_i_2276_, v_a_2277_);
lean_dec_ref(v_as_2275_);
lean_dec(v_userName_2274_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(lean_object* v_userName_2279_, lean_object* v_as_2280_, lean_object* v_i_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___redArg(v_userName_2279_, v_as_2280_, v_i_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2___boxed(lean_object* v_userName_2284_, lean_object* v_as_2285_, lean_object* v_i_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findFromUserName_x3f_spec__0_spec__1_spec__2(v_userName_2284_, v_as_2285_, v_i_2286_, v_a_2287_);
lean_dec_ref(v_as_2285_);
lean_dec(v_userName_2284_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21(lean_object* v_lctx_2292_, lean_object* v_userName_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2292_, v_userName_2293_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2295_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_2296_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__0));
v___x_2297_ = lean_unsigned_to_nat(403u);
v___x_2298_ = lean_unsigned_to_nat(17u);
v___x_2299_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__1));
v___x_2300_ = 1;
v___x_2301_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_2293_, v___x_2300_);
v___x_2302_ = lean_string_append(v___x_2299_, v___x_2301_);
lean_dec_ref(v___x_2301_);
v___x_2303_ = ((lean_object*)(l_Lean_LocalContext_getFromUserName_x21___closed__2));
v___x_2304_ = lean_string_append(v___x_2302_, v___x_2303_);
v___x_2305_ = l_mkPanicMessageWithDecl(v___x_2295_, v___x_2296_, v___x_2297_, v___x_2298_, v___x_2304_);
lean_dec_ref(v___x_2304_);
v___x_2306_ = l_panic___at___00Lean_LocalDecl_setBinderInfo_spec__0(v___x_2305_);
return v___x_2306_;
}
else
{
lean_object* v_val_2307_; 
lean_dec(v_userName_2293_);
v_val_2307_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_val_2307_);
lean_dec_ref_known(v___x_2294_, 1);
return v_val_2307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getFromUserName_x21___boxed(lean_object* v_lctx_2308_, lean_object* v_userName_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_LocalContext_getFromUserName_x21(v_lctx_2308_, v_userName_2309_);
lean_dec_ref(v_lctx_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_usesUserName(lean_object* v_lctx_2311_, lean_object* v_userName_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2311_, v_userName_2312_);
if (lean_obj_tag(v___x_2313_) == 0)
{
uint8_t v___x_2314_; 
v___x_2314_ = 0;
return v___x_2314_;
}
else
{
uint8_t v___x_2315_; 
lean_dec_ref_known(v___x_2313_, 1);
v___x_2315_ = 1;
return v___x_2315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_usesUserName___boxed(lean_object* v_lctx_2316_, lean_object* v_userName_2317_){
_start:
{
uint8_t v_res_2318_; lean_object* v_r_2319_; 
v_res_2318_ = l_Lean_LocalContext_usesUserName(v_lctx_2316_, v_userName_2317_);
lean_dec(v_userName_2317_);
lean_dec_ref(v_lctx_2316_);
v_r_2319_ = lean_box(v_res_2318_);
return v_r_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(lean_object* v_lctx_2320_, lean_object* v_suggestion_2321_, lean_object* v_i_2322_){
_start:
{
lean_object* v_curr_2323_; uint8_t v___x_2324_; 
lean_inc(v_i_2322_);
lean_inc(v_suggestion_2321_);
v_curr_2323_ = lean_name_append_index_after(v_suggestion_2321_, v_i_2322_);
v___x_2324_ = l_Lean_LocalContext_usesUserName(v_lctx_2320_, v_curr_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec(v_suggestion_2321_);
v___x_2325_ = lean_unsigned_to_nat(1u);
v___x_2326_ = lean_nat_add(v_i_2322_, v___x_2325_);
lean_dec(v_i_2322_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v_curr_2323_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
return v___x_2327_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec(v_curr_2323_);
v___x_2328_ = lean_unsigned_to_nat(1u);
v___x_2329_ = lean_nat_add(v_i_2322_, v___x_2328_);
lean_dec(v_i_2322_);
v_i_2322_ = v___x_2329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux___boxed(lean_object* v_lctx_2331_, lean_object* v_suggestion_2332_, lean_object* v_i_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2331_, v_suggestion_2332_, v_i_2333_);
lean_dec_ref(v_lctx_2331_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName(lean_object* v_lctx_2335_, lean_object* v_suggestion_2336_){
_start:
{
lean_object* v_suggestion_2337_; uint8_t v___x_2338_; 
v_suggestion_2337_ = l_Lean_Name_eraseMacroScopes(v_suggestion_2336_);
v___x_2338_ = l_Lean_LocalContext_usesUserName(v_lctx_2335_, v_suggestion_2337_);
if (v___x_2338_ == 0)
{
return v_suggestion_2337_;
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v_fst_2341_; 
v___x_2339_ = lean_unsigned_to_nat(1u);
v___x_2340_ = l___private_Lean_LocalContext_0__Lean_LocalContext_getUnusedNameAux(v_lctx_2335_, v_suggestion_2337_, v___x_2339_);
v_fst_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_fst_2341_);
lean_dec_ref(v___x_2340_);
return v_fst_2341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getUnusedName___boxed(lean_object* v_lctx_2342_, lean_object* v_suggestion_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_LocalContext_getUnusedName(v_lctx_2342_, v_suggestion_2343_);
lean_dec(v_suggestion_2343_);
lean_dec_ref(v_lctx_2342_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl(lean_object* v_lctx_2345_){
_start:
{
lean_object* v_decls_2346_; lean_object* v_size_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_decls_2346_ = lean_ctor_get(v_lctx_2345_, 1);
v_size_2347_ = lean_ctor_get(v_decls_2346_, 2);
v___x_2348_ = lean_box(0);
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_nat_sub(v_size_2347_, v___x_2349_);
v___x_2351_ = lean_nat_dec_lt(v___x_2350_, v_size_2347_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; 
lean_dec(v___x_2350_);
v___x_2352_ = l_outOfBounds___redArg(v___x_2348_);
return v___x_2352_;
}
else
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2348_, v_decls_2346_, v___x_2350_);
lean_dec(v___x_2350_);
return v___x_2353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_lastDecl___boxed(lean_object* v_lctx_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_LocalContext_lastDecl(v_lctx_2354_);
lean_dec_ref(v_lctx_2354_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setUserName(lean_object* v_lctx_2356_, lean_object* v_fvarId_2357_, lean_object* v_userName_2358_){
_start:
{
lean_object* v_fvarIdToDecl_2359_; lean_object* v_decls_2360_; lean_object* v_auxDeclToFullName_2361_; lean_object* v_decl_2362_; lean_object* v_decl_2363_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2371_; lean_object* v_fvarId_2374_; 
v_fvarIdToDecl_2359_ = lean_ctor_get(v_lctx_2356_, 0);
lean_inc_ref(v_fvarIdToDecl_2359_);
v_decls_2360_ = lean_ctor_get(v_lctx_2356_, 1);
lean_inc_ref(v_decls_2360_);
v_auxDeclToFullName_2361_ = lean_ctor_get(v_lctx_2356_, 2);
lean_inc(v_auxDeclToFullName_2361_);
v_decl_2362_ = l_Lean_LocalContext_get_x21(v_lctx_2356_, v_fvarId_2357_);
v_decl_2363_ = l_Lean_LocalDecl_setUserName(v_decl_2362_, v_userName_2358_);
v_fvarId_2374_ = lean_ctor_get(v_decl_2363_, 1);
lean_inc(v_fvarId_2374_);
v___y_2371_ = v_fvarId_2374_;
goto v___jp_2370_;
v___jp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v_decl_2363_);
v___x_2368_ = l_Lean_PersistentArray_set___redArg(v_decls_2360_, v___y_2366_, v___x_2367_);
lean_dec(v___y_2366_);
v___x_2369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2369_, 0, v___y_2365_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
lean_ctor_set(v___x_2369_, 2, v_auxDeclToFullName_2361_);
return v___x_2369_;
}
v___jp_2370_:
{
lean_object* v___x_2372_; lean_object* v_index_2373_; 
lean_inc_ref(v_decl_2363_);
v___x_2372_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2359_, v___y_2371_, v_decl_2363_);
v_index_2373_ = lean_ctor_get(v_decl_2363_, 0);
lean_inc(v_index_2373_);
v___y_2365_ = v___x_2372_;
v___y_2366_ = v_index_2373_;
goto v___jp_2364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName(lean_object* v_lctx_2375_, lean_object* v_fromName_2376_, lean_object* v_toName_2377_){
_start:
{
lean_object* v_fvarIdToDecl_2378_; lean_object* v_decls_2379_; lean_object* v_auxDeclToFullName_2380_; lean_object* v___x_2381_; 
v_fvarIdToDecl_2378_ = lean_ctor_get(v_lctx_2375_, 0);
v_decls_2379_ = lean_ctor_get(v_lctx_2375_, 1);
v_auxDeclToFullName_2380_ = lean_ctor_get(v_lctx_2375_, 2);
v___x_2381_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_2375_, v_fromName_2376_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_dec(v_toName_2377_);
return v_lctx_2375_;
}
else
{
lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2406_; 
lean_inc(v_auxDeclToFullName_2380_);
lean_inc_ref(v_decls_2379_);
lean_inc_ref(v_fvarIdToDecl_2378_);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_lctx_2375_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; lean_object* v_unused_2408_; lean_object* v_unused_2409_; 
v_unused_2407_ = lean_ctor_get(v_lctx_2375_, 2);
lean_dec(v_unused_2407_);
v_unused_2408_ = lean_ctor_get(v_lctx_2375_, 1);
lean_dec(v_unused_2408_);
v_unused_2409_ = lean_ctor_get(v_lctx_2375_, 0);
lean_dec(v_unused_2409_);
v___x_2383_ = v_lctx_2375_;
v_isShared_2384_ = v_isSharedCheck_2406_;
goto v_resetjp_2382_;
}
else
{
lean_dec(v_lctx_2375_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2406_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v_val_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2405_; 
v_val_2385_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2387_ = v___x_2381_;
v_isShared_2388_ = v_isSharedCheck_2405_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_val_2385_);
lean_dec(v___x_2381_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2405_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_decl_2389_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2401_; lean_object* v_fvarId_2404_; 
v_decl_2389_ = l_Lean_LocalDecl_setUserName(v_val_2385_, v_toName_2377_);
v_fvarId_2404_ = lean_ctor_get(v_decl_2389_, 1);
lean_inc(v_fvarId_2404_);
v___y_2401_ = v_fvarId_2404_;
goto v___jp_2400_;
v___jp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v_decl_2389_);
v___x_2394_ = v___x_2387_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_decl_2389_);
v___x_2394_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2395_ = l_Lean_PersistentArray_set___redArg(v_decls_2379_, v___y_2392_, v___x_2394_);
lean_dec(v___y_2392_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 1, v___x_2395_);
lean_ctor_set(v___x_2383_, 0, v___y_2391_);
v___x_2397_ = v___x_2383_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___y_2391_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_auxDeclToFullName_2380_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
v___jp_2400_:
{
lean_object* v___x_2402_; lean_object* v_index_2403_; 
lean_inc_ref(v_decl_2389_);
v___x_2402_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2378_, v___y_2401_, v_decl_2389_);
v_index_2403_ = lean_ctor_get(v_decl_2389_, 0);
lean_inc(v_index_2403_);
v___y_2391_ = v___x_2402_;
v___y_2392_ = v_index_2403_;
goto v___jp_2390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_renameUserName___boxed(lean_object* v_lctx_2410_, lean_object* v_fromName_2411_, lean_object* v_toName_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_LocalContext_renameUserName(v_lctx_2410_, v_fromName_2411_, v_toName_2412_);
lean_dec(v_fromName_2411_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecl(lean_object* v_lctx_2416_, lean_object* v_fvarId_2417_, lean_object* v_f_2418_){
_start:
{
lean_object* v_fvarIdToDecl_2419_; lean_object* v_decls_2420_; lean_object* v_auxDeclToFullName_2421_; lean_object* v___x_2422_; 
v_fvarIdToDecl_2419_ = lean_ctor_get(v_lctx_2416_, 0);
v_decls_2420_ = lean_ctor_get(v_lctx_2416_, 1);
v_auxDeclToFullName_2421_ = lean_ctor_get(v_lctx_2416_, 2);
lean_inc_ref(v_lctx_2416_);
v___x_2422_ = lean_local_ctx_find(v_lctx_2416_, v_fvarId_2417_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_dec_ref(v_f_2418_);
return v_lctx_2416_;
}
else
{
lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2449_; 
lean_inc(v_auxDeclToFullName_2421_);
lean_inc_ref(v_decls_2420_);
lean_inc_ref(v_fvarIdToDecl_2419_);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_lctx_2416_);
if (v_isSharedCheck_2449_ == 0)
{
lean_object* v_unused_2450_; lean_object* v_unused_2451_; lean_object* v_unused_2452_; 
v_unused_2450_ = lean_ctor_get(v_lctx_2416_, 2);
lean_dec(v_unused_2450_);
v_unused_2451_ = lean_ctor_get(v_lctx_2416_, 1);
lean_dec(v_unused_2451_);
v_unused_2452_ = lean_ctor_get(v_lctx_2416_, 0);
lean_dec(v_unused_2452_);
v___x_2424_ = v_lctx_2416_;
v_isShared_2425_ = v_isSharedCheck_2449_;
goto v_resetjp_2423_;
}
else
{
lean_dec(v_lctx_2416_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2449_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v_val_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2448_; 
v_val_2426_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2428_ = v___x_2422_;
v_isShared_2429_ = v_isSharedCheck_2448_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_val_2426_);
lean_dec(v___x_2422_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2448_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_decl_2432_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2444_; lean_object* v_fvarId_2447_; 
v___x_2430_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__0));
v___x_2431_ = ((lean_object*)(l_Lean_LocalContext_modifyLocalDecl___closed__1));
v_decl_2432_ = lean_apply_1(v_f_2418_, v_val_2426_);
v_fvarId_2447_ = lean_ctor_get(v_decl_2432_, 1);
lean_inc(v_fvarId_2447_);
v___y_2444_ = v_fvarId_2447_;
goto v___jp_2443_;
v___jp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v_decl_2432_);
v___x_2437_ = v___x_2428_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_decl_2432_);
v___x_2437_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2438_ = l_Lean_PersistentArray_set___redArg(v_decls_2420_, v___y_2435_, v___x_2437_);
lean_dec(v___y_2435_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 1, v___x_2438_);
lean_ctor_set(v___x_2424_, 0, v___y_2434_);
v___x_2440_ = v___x_2424_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___y_2434_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2441_, 2, v_auxDeclToFullName_2421_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
v___jp_2443_:
{
lean_object* v___x_2445_; lean_object* v_index_2446_; 
lean_inc_ref(v_decl_2432_);
v___x_2445_ = l_Lean_PersistentHashMap_insert___redArg(v___x_2430_, v___x_2431_, v_fvarIdToDecl_2419_, v___y_2444_, v_decl_2432_);
v_index_2446_ = lean_ctor_get(v_decl_2432_, 0);
lean_inc(v_index_2446_);
v___y_2434_ = v___x_2445_;
v___y_2435_ = v_index_2446_;
goto v___jp_2433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(lean_object* v_f_2453_, lean_object* v_as_2454_, size_t v_i_2455_, size_t v_stop_2456_, lean_object* v_b_2457_){
_start:
{
lean_object* v___y_2459_; uint8_t v___x_2463_; 
v___x_2463_ = lean_usize_dec_eq(v_i_2455_, v_stop_2456_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_array_uget(v_as_2454_, v_i_2455_);
if (lean_obj_tag(v___x_2464_) == 0)
{
v___y_2459_ = v_b_2457_;
goto v___jp_2458_;
}
else
{
lean_object* v_val_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2492_; 
v_val_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2492_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_val_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2492_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v_fvarIdToDecl_2469_; lean_object* v_decls_2470_; lean_object* v_auxDeclToFullName_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2491_; 
v_fvarIdToDecl_2469_ = lean_ctor_get(v_b_2457_, 0);
v_decls_2470_ = lean_ctor_get(v_b_2457_, 1);
v_auxDeclToFullName_2471_ = lean_ctor_get(v_b_2457_, 2);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_b_2457_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2473_ = v_b_2457_;
v_isShared_2474_ = v_isSharedCheck_2491_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_auxDeclToFullName_2471_);
lean_inc(v_decls_2470_);
lean_inc(v_fvarIdToDecl_2469_);
lean_dec(v_b_2457_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2491_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v_decl_2475_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2487_; lean_object* v_fvarId_2490_; 
lean_inc_ref(v_f_2453_);
v_decl_2475_ = lean_apply_1(v_f_2453_, v_val_2465_);
v_fvarId_2490_ = lean_ctor_get(v_decl_2475_, 1);
lean_inc(v_fvarId_2490_);
v___y_2487_ = v_fvarId_2490_;
goto v___jp_2486_;
v___jp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v_decl_2475_);
v___x_2480_ = v___x_2467_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_decl_2475_);
v___x_2480_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = l_Lean_PersistentArray_set___redArg(v_decls_2470_, v___y_2478_, v___x_2480_);
lean_dec(v___y_2478_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 1, v___x_2481_);
lean_ctor_set(v___x_2473_, 0, v___y_2477_);
v___x_2483_ = v___x_2473_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___y_2477_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2484_, 2, v_auxDeclToFullName_2471_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
v___y_2459_ = v___x_2483_;
goto v___jp_2458_;
}
}
}
v___jp_2486_:
{
lean_object* v___x_2488_; lean_object* v_index_2489_; 
lean_inc_ref(v_decl_2475_);
v___x_2488_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2469_, v___y_2487_, v_decl_2475_);
v_index_2489_ = lean_ctor_get(v_decl_2475_, 0);
lean_inc(v_index_2489_);
v___y_2477_ = v___x_2488_;
v___y_2478_ = v_index_2489_;
goto v___jp_2476_;
}
}
}
}
}
else
{
lean_dec_ref(v_f_2453_);
return v_b_2457_;
}
v___jp_2458_:
{
size_t v___x_2460_; size_t v___x_2461_; 
v___x_2460_ = ((size_t)1ULL);
v___x_2461_ = lean_usize_add(v_i_2455_, v___x_2460_);
v_i_2455_ = v___x_2461_;
v_b_2457_ = v___y_2459_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1___boxed(lean_object* v_f_2493_, lean_object* v_as_2494_, lean_object* v_i_2495_, lean_object* v_stop_2496_, lean_object* v_b_2497_){
_start:
{
size_t v_i_boxed_2498_; size_t v_stop_boxed_2499_; lean_object* v_res_2500_; 
v_i_boxed_2498_ = lean_unbox_usize(v_i_2495_);
lean_dec(v_i_2495_);
v_stop_boxed_2499_ = lean_unbox_usize(v_stop_2496_);
lean_dec(v_stop_2496_);
v_res_2500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2493_, v_as_2494_, v_i_boxed_2498_, v_stop_boxed_2499_, v_b_2497_);
lean_dec_ref(v_as_2494_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(lean_object* v_f_2501_, lean_object* v_x_2502_, lean_object* v_x_2503_){
_start:
{
if (lean_obj_tag(v_x_2502_) == 0)
{
lean_object* v_cs_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v_cs_2504_ = lean_ctor_get(v_x_2502_, 0);
v___x_2505_ = lean_unsigned_to_nat(0u);
v___x_2506_ = lean_array_get_size(v_cs_2504_);
v___x_2507_ = lean_nat_dec_lt(v___x_2505_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_dec_ref(v_f_2501_);
return v_x_2503_;
}
else
{
size_t v___x_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = ((size_t)0ULL);
v___x_2509_ = lean_usize_of_nat(v___x_2506_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2501_, v_cs_2504_, v___x_2508_, v___x_2509_, v_x_2503_);
return v___x_2510_;
}
}
else
{
lean_object* v_vs_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v_vs_2511_ = lean_ctor_get(v_x_2502_, 0);
v___x_2512_ = lean_unsigned_to_nat(0u);
v___x_2513_ = lean_array_get_size(v_vs_2511_);
v___x_2514_ = lean_nat_dec_lt(v___x_2512_, v___x_2513_);
if (v___x_2514_ == 0)
{
lean_dec_ref(v_f_2501_);
return v_x_2503_;
}
else
{
size_t v___x_2515_; size_t v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = ((size_t)0ULL);
v___x_2516_ = lean_usize_of_nat(v___x_2513_);
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2501_, v_vs_2511_, v___x_2515_, v___x_2516_, v_x_2503_);
return v___x_2517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(lean_object* v_f_2518_, lean_object* v_as_2519_, size_t v_i_2520_, size_t v_stop_2521_, lean_object* v_b_2522_){
_start:
{
uint8_t v___x_2523_; 
v___x_2523_ = lean_usize_dec_eq(v_i_2520_, v_stop_2521_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; lean_object* v___x_2525_; size_t v___x_2526_; size_t v___x_2527_; 
v___x_2524_ = lean_array_uget_borrowed(v_as_2519_, v_i_2520_);
lean_inc_ref(v_f_2518_);
v___x_2525_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2518_, v___x_2524_, v_b_2522_);
v___x_2526_ = ((size_t)1ULL);
v___x_2527_ = lean_usize_add(v_i_2520_, v___x_2526_);
v_i_2520_ = v___x_2527_;
v_b_2522_ = v___x_2525_;
goto _start;
}
else
{
lean_dec_ref(v_f_2518_);
return v_b_2522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2529_, lean_object* v_as_2530_, lean_object* v_i_2531_, lean_object* v_stop_2532_, lean_object* v_b_2533_){
_start:
{
size_t v_i_boxed_2534_; size_t v_stop_boxed_2535_; lean_object* v_res_2536_; 
v_i_boxed_2534_ = lean_unbox_usize(v_i_2531_);
lean_dec(v_i_2531_);
v_stop_boxed_2535_ = lean_unbox_usize(v_stop_2532_);
lean_dec(v_stop_2532_);
v_res_2536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2529_, v_as_2530_, v_i_boxed_2534_, v_stop_boxed_2535_, v_b_2533_);
lean_dec_ref(v_as_2530_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2___boxed(lean_object* v_f_2537_, lean_object* v_x_2538_, lean_object* v_x_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2537_, v_x_2538_, v_x_2539_);
lean_dec_ref(v_x_2538_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(lean_object* v_f_2541_, lean_object* v_x_2542_, size_t v_x_2543_, size_t v_x_2544_, lean_object* v_x_2545_){
_start:
{
if (lean_obj_tag(v_x_2542_) == 0)
{
lean_object* v_cs_2546_; lean_object* v___x_2547_; size_t v___x_2548_; lean_object* v_j_2549_; lean_object* v___x_2550_; size_t v___x_2551_; size_t v___x_2552_; size_t v___x_2553_; size_t v___x_2554_; size_t v___x_2555_; size_t v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v_cs_2546_ = lean_ctor_get(v_x_2542_, 0);
v___x_2547_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_2548_ = lean_usize_shift_right(v_x_2543_, v_x_2544_);
v_j_2549_ = lean_usize_to_nat(v___x_2548_);
v___x_2550_ = lean_array_get_borrowed(v___x_2547_, v_cs_2546_, v_j_2549_);
v___x_2551_ = ((size_t)1ULL);
v___x_2552_ = lean_usize_shift_left(v___x_2551_, v_x_2544_);
v___x_2553_ = lean_usize_sub(v___x_2552_, v___x_2551_);
v___x_2554_ = lean_usize_land(v_x_2543_, v___x_2553_);
v___x_2555_ = ((size_t)5ULL);
v___x_2556_ = lean_usize_sub(v_x_2544_, v___x_2555_);
lean_inc_ref(v_f_2541_);
v___x_2557_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2541_, v___x_2550_, v___x_2554_, v___x_2556_, v_x_2545_);
v___x_2558_ = lean_unsigned_to_nat(1u);
v___x_2559_ = lean_nat_add(v_j_2549_, v___x_2558_);
lean_dec(v_j_2549_);
v___x_2560_ = lean_array_get_size(v_cs_2546_);
v___x_2561_ = lean_nat_dec_lt(v___x_2559_, v___x_2560_);
if (v___x_2561_ == 0)
{
lean_dec(v___x_2559_);
lean_dec_ref(v_f_2541_);
return v___x_2557_;
}
else
{
size_t v___x_2562_; size_t v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = lean_usize_of_nat(v___x_2559_);
lean_dec(v___x_2559_);
v___x_2563_ = lean_usize_of_nat(v___x_2560_);
v___x_2564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0_spec__1(v_f_2541_, v_cs_2546_, v___x_2562_, v___x_2563_, v___x_2557_);
return v___x_2564_;
}
}
else
{
lean_object* v_vs_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v_vs_2565_ = lean_ctor_get(v_x_2542_, 0);
v___x_2566_ = lean_usize_to_nat(v_x_2543_);
v___x_2567_ = lean_array_get_size(v_vs_2565_);
v___x_2568_ = lean_nat_dec_lt(v___x_2566_, v___x_2567_);
if (v___x_2568_ == 0)
{
lean_dec(v___x_2566_);
lean_dec_ref(v_f_2541_);
return v_x_2545_;
}
else
{
size_t v___x_2569_; size_t v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_usize_of_nat(v___x_2566_);
lean_dec(v___x_2566_);
v___x_2570_ = lean_usize_of_nat(v___x_2567_);
v___x_2571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2541_, v_vs_2565_, v___x_2569_, v___x_2570_, v_x_2545_);
return v___x_2571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0___boxed(lean_object* v_f_2572_, lean_object* v_x_2573_, lean_object* v_x_2574_, lean_object* v_x_2575_, lean_object* v_x_2576_){
_start:
{
size_t v_x_1487__boxed_2577_; size_t v_x_1488__boxed_2578_; lean_object* v_res_2579_; 
v_x_1487__boxed_2577_ = lean_unbox_usize(v_x_2574_);
lean_dec(v_x_2574_);
v_x_1488__boxed_2578_ = lean_unbox_usize(v_x_2575_);
lean_dec(v_x_2575_);
v_res_2579_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2572_, v_x_2573_, v_x_1487__boxed_2577_, v_x_1488__boxed_2578_, v_x_2576_);
lean_dec_ref(v_x_2573_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(lean_object* v_f_2580_, lean_object* v_t_2581_, lean_object* v_init_2582_, lean_object* v_start_2583_){
_start:
{
lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2584_ = lean_unsigned_to_nat(0u);
v___x_2585_ = lean_nat_dec_eq(v_start_2583_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v_root_2586_; lean_object* v_tail_2587_; size_t v_shift_2588_; lean_object* v_tailOff_2589_; uint8_t v___x_2590_; 
v_root_2586_ = lean_ctor_get(v_t_2581_, 0);
v_tail_2587_ = lean_ctor_get(v_t_2581_, 1);
v_shift_2588_ = lean_ctor_get_usize(v_t_2581_, 4);
v_tailOff_2589_ = lean_ctor_get(v_t_2581_, 3);
v___x_2590_ = lean_nat_dec_le(v_tailOff_2589_, v_start_2583_);
if (v___x_2590_ == 0)
{
size_t v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2591_ = lean_usize_of_nat(v_start_2583_);
lean_inc_ref(v_f_2580_);
v___x_2592_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__0(v_f_2580_, v_root_2586_, v___x_2591_, v_shift_2588_, v_init_2582_);
v___x_2593_ = lean_array_get_size(v_tail_2587_);
v___x_2594_ = lean_nat_dec_lt(v___x_2584_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_dec_ref(v_f_2580_);
return v___x_2592_;
}
else
{
size_t v___x_2595_; size_t v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = ((size_t)0ULL);
v___x_2596_ = lean_usize_of_nat(v___x_2593_);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2580_, v_tail_2587_, v___x_2595_, v___x_2596_, v___x_2592_);
return v___x_2597_;
}
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2598_ = lean_nat_sub(v_start_2583_, v_tailOff_2589_);
v___x_2599_ = lean_array_get_size(v_tail_2587_);
v___x_2600_ = lean_nat_dec_lt(v___x_2598_, v___x_2599_);
if (v___x_2600_ == 0)
{
lean_dec(v___x_2598_);
lean_dec_ref(v_f_2580_);
return v_init_2582_;
}
else
{
size_t v___x_2601_; size_t v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = lean_usize_of_nat(v___x_2598_);
lean_dec(v___x_2598_);
v___x_2602_ = lean_usize_of_nat(v___x_2599_);
v___x_2603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2580_, v_tail_2587_, v___x_2601_, v___x_2602_, v_init_2582_);
return v___x_2603_;
}
}
}
else
{
lean_object* v_root_2604_; lean_object* v_tail_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; 
v_root_2604_ = lean_ctor_get(v_t_2581_, 0);
v_tail_2605_ = lean_ctor_get(v_t_2581_, 1);
lean_inc_ref(v_f_2580_);
v___x_2606_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__2(v_f_2580_, v_root_2604_, v_init_2582_);
v___x_2607_ = lean_array_get_size(v_tail_2605_);
v___x_2608_ = lean_nat_dec_lt(v___x_2584_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_dec_ref(v_f_2580_);
return v___x_2606_;
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = ((size_t)0ULL);
v___x_2610_ = lean_usize_of_nat(v___x_2607_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0_spec__1(v_f_2580_, v_tail_2605_, v___x_2609_, v___x_2610_, v___x_2606_);
return v___x_2611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0___boxed(lean_object* v_f_2612_, lean_object* v_t_2613_, lean_object* v_init_2614_, lean_object* v_start_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2612_, v_t_2613_, v_init_2614_, v_start_2615_);
lean_dec(v_start_2615_);
lean_dec_ref(v_t_2613_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_modifyLocalDecls(lean_object* v_lctx_2617_, lean_object* v_f_2618_){
_start:
{
lean_object* v_decls_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v_decls_2619_ = lean_ctor_get(v_lctx_2617_, 1);
lean_inc_ref(v_decls_2619_);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_modifyLocalDecls_spec__0(v_f_2618_, v_decls_2619_, v_lctx_2617_, v___x_2620_);
lean_dec_ref(v_decls_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind(lean_object* v_lctx_2622_, lean_object* v_fvarId_2623_, uint8_t v_kind_2624_){
_start:
{
lean_object* v_fvarIdToDecl_2625_; lean_object* v_decls_2626_; lean_object* v_auxDeclToFullName_2627_; lean_object* v___x_2628_; 
v_fvarIdToDecl_2625_ = lean_ctor_get(v_lctx_2622_, 0);
v_decls_2626_ = lean_ctor_get(v_lctx_2622_, 1);
v_auxDeclToFullName_2627_ = lean_ctor_get(v_lctx_2622_, 2);
lean_inc_ref(v_lctx_2622_);
v___x_2628_ = lean_local_ctx_find(v_lctx_2622_, v_fvarId_2623_);
if (lean_obj_tag(v___x_2628_) == 0)
{
return v_lctx_2622_;
}
else
{
lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2653_; 
lean_inc(v_auxDeclToFullName_2627_);
lean_inc_ref(v_decls_2626_);
lean_inc_ref(v_fvarIdToDecl_2625_);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_lctx_2622_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; lean_object* v_unused_2655_; lean_object* v_unused_2656_; 
v_unused_2654_ = lean_ctor_get(v_lctx_2622_, 2);
lean_dec(v_unused_2654_);
v_unused_2655_ = lean_ctor_get(v_lctx_2622_, 1);
lean_dec(v_unused_2655_);
v_unused_2656_ = lean_ctor_get(v_lctx_2622_, 0);
lean_dec(v_unused_2656_);
v___x_2630_ = v_lctx_2622_;
v_isShared_2631_ = v_isSharedCheck_2653_;
goto v_resetjp_2629_;
}
else
{
lean_dec(v_lctx_2622_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2653_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v_val_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2652_; 
v_val_2632_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2634_ = v___x_2628_;
v_isShared_2635_ = v_isSharedCheck_2652_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_val_2632_);
lean_dec(v___x_2628_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2652_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_decl_2636_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2648_; lean_object* v_fvarId_2651_; 
v_decl_2636_ = l_Lean_LocalDecl_setKind(v_val_2632_, v_kind_2624_);
v_fvarId_2651_ = lean_ctor_get(v_decl_2636_, 1);
lean_inc(v_fvarId_2651_);
v___y_2648_ = v_fvarId_2651_;
goto v___jp_2647_;
v___jp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v_decl_2636_);
v___x_2641_ = v___x_2634_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_decl_2636_);
v___x_2641_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2642_ = l_Lean_PersistentArray_set___redArg(v_decls_2626_, v___y_2639_, v___x_2641_);
lean_dec(v___y_2639_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 1, v___x_2642_);
lean_ctor_set(v___x_2630_, 0, v___y_2638_);
v___x_2644_ = v___x_2630_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___y_2638_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2645_, 2, v_auxDeclToFullName_2627_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
v___jp_2647_:
{
lean_object* v___x_2649_; lean_object* v_index_2650_; 
lean_inc_ref(v_decl_2636_);
v___x_2649_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2625_, v___y_2648_, v_decl_2636_);
v_index_2650_ = lean_ctor_get(v_decl_2636_, 0);
lean_inc(v_index_2650_);
v___y_2638_ = v___x_2649_;
v___y_2639_ = v_index_2650_;
goto v___jp_2637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setKind___boxed(lean_object* v_lctx_2657_, lean_object* v_fvarId_2658_, lean_object* v_kind_2659_){
_start:
{
uint8_t v_kind_boxed_2660_; lean_object* v_res_2661_; 
v_kind_boxed_2660_ = lean_unbox(v_kind_2659_);
v_res_2661_ = l_Lean_LocalContext_setKind(v_lctx_2657_, v_fvarId_2658_, v_kind_boxed_2660_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo(lean_object* v_lctx_2662_, lean_object* v_fvarId_2663_, uint8_t v_bi_2664_){
_start:
{
lean_object* v_fvarIdToDecl_2665_; lean_object* v_decls_2666_; lean_object* v_auxDeclToFullName_2667_; lean_object* v___x_2668_; 
v_fvarIdToDecl_2665_ = lean_ctor_get(v_lctx_2662_, 0);
v_decls_2666_ = lean_ctor_get(v_lctx_2662_, 1);
v_auxDeclToFullName_2667_ = lean_ctor_get(v_lctx_2662_, 2);
lean_inc_ref(v_lctx_2662_);
v___x_2668_ = lean_local_ctx_find(v_lctx_2662_, v_fvarId_2663_);
if (lean_obj_tag(v___x_2668_) == 0)
{
return v_lctx_2662_;
}
else
{
lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2693_; 
lean_inc(v_auxDeclToFullName_2667_);
lean_inc_ref(v_decls_2666_);
lean_inc_ref(v_fvarIdToDecl_2665_);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_lctx_2662_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; lean_object* v_unused_2695_; lean_object* v_unused_2696_; 
v_unused_2694_ = lean_ctor_get(v_lctx_2662_, 2);
lean_dec(v_unused_2694_);
v_unused_2695_ = lean_ctor_get(v_lctx_2662_, 1);
lean_dec(v_unused_2695_);
v_unused_2696_ = lean_ctor_get(v_lctx_2662_, 0);
lean_dec(v_unused_2696_);
v___x_2670_ = v_lctx_2662_;
v_isShared_2671_ = v_isSharedCheck_2693_;
goto v_resetjp_2669_;
}
else
{
lean_dec(v_lctx_2662_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2693_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_val_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2692_; 
v_val_2672_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2674_ = v___x_2668_;
v_isShared_2675_ = v_isSharedCheck_2692_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_val_2672_);
lean_dec(v___x_2668_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2692_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v_decl_2676_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2688_; lean_object* v_fvarId_2691_; 
v_decl_2676_ = l_Lean_LocalDecl_setBinderInfo(v_val_2672_, v_bi_2664_);
v_fvarId_2691_ = lean_ctor_get(v_decl_2676_, 1);
lean_inc(v_fvarId_2691_);
v___y_2688_ = v_fvarId_2691_;
goto v___jp_2687_;
v___jp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v_decl_2676_);
v___x_2681_ = v___x_2674_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_decl_2676_);
v___x_2681_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2682_ = l_Lean_PersistentArray_set___redArg(v_decls_2666_, v___y_2679_, v___x_2681_);
lean_dec(v___y_2679_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___x_2682_);
lean_ctor_set(v___x_2670_, 0, v___y_2678_);
v___x_2684_ = v___x_2670_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___y_2678_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2685_, 2, v_auxDeclToFullName_2667_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
v___jp_2687_:
{
lean_object* v___x_2689_; lean_object* v_index_2690_; 
lean_inc_ref(v_decl_2676_);
v___x_2689_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2665_, v___y_2688_, v_decl_2676_);
v_index_2690_ = lean_ctor_get(v_decl_2676_, 0);
lean_inc(v_index_2690_);
v___y_2678_ = v___x_2689_;
v___y_2679_ = v_index_2690_;
goto v___jp_2677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setBinderInfo___boxed(lean_object* v_lctx_2697_, lean_object* v_fvarId_2698_, lean_object* v_bi_2699_){
_start:
{
uint8_t v_bi_boxed_2700_; lean_object* v_res_2701_; 
v_bi_boxed_2700_ = lean_unbox(v_bi_2699_);
v_res_2701_ = l_Lean_LocalContext_setBinderInfo(v_lctx_2697_, v_fvarId_2698_, v_bi_boxed_2700_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_setType(lean_object* v_lctx_2702_, lean_object* v_fvarId_2703_, lean_object* v_type_2704_){
_start:
{
lean_object* v_fvarIdToDecl_2705_; lean_object* v_decls_2706_; lean_object* v_auxDeclToFullName_2707_; lean_object* v___x_2708_; 
v_fvarIdToDecl_2705_ = lean_ctor_get(v_lctx_2702_, 0);
v_decls_2706_ = lean_ctor_get(v_lctx_2702_, 1);
v_auxDeclToFullName_2707_ = lean_ctor_get(v_lctx_2702_, 2);
lean_inc_ref(v_lctx_2702_);
v___x_2708_ = lean_local_ctx_find(v_lctx_2702_, v_fvarId_2703_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_dec_ref(v_type_2704_);
return v_lctx_2702_;
}
else
{
lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2733_; 
lean_inc(v_auxDeclToFullName_2707_);
lean_inc_ref(v_decls_2706_);
lean_inc_ref(v_fvarIdToDecl_2705_);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_lctx_2702_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; lean_object* v_unused_2735_; lean_object* v_unused_2736_; 
v_unused_2734_ = lean_ctor_get(v_lctx_2702_, 2);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_lctx_2702_, 1);
lean_dec(v_unused_2735_);
v_unused_2736_ = lean_ctor_get(v_lctx_2702_, 0);
lean_dec(v_unused_2736_);
v___x_2710_ = v_lctx_2702_;
v_isShared_2711_ = v_isSharedCheck_2733_;
goto v_resetjp_2709_;
}
else
{
lean_dec(v_lctx_2702_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2733_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v_val_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2732_; 
v_val_2712_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2714_ = v___x_2708_;
v_isShared_2715_ = v_isSharedCheck_2732_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_val_2712_);
lean_dec(v___x_2708_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2732_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v_decl_2716_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2728_; lean_object* v_fvarId_2731_; 
v_decl_2716_ = l_Lean_LocalDecl_setType(v_val_2712_, v_type_2704_);
v_fvarId_2731_ = lean_ctor_get(v_decl_2716_, 1);
lean_inc(v_fvarId_2731_);
v___y_2728_ = v_fvarId_2731_;
goto v___jp_2727_;
v___jp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v_decl_2716_);
v___x_2721_ = v___x_2714_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_decl_2716_);
v___x_2721_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2722_ = l_Lean_PersistentArray_set___redArg(v_decls_2706_, v___y_2719_, v___x_2721_);
lean_dec(v___y_2719_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 1, v___x_2722_);
lean_ctor_set(v___x_2710_, 0, v___y_2718_);
v___x_2724_ = v___x_2710_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___y_2718_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_auxDeclToFullName_2707_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
v___jp_2727_:
{
lean_object* v___x_2729_; lean_object* v_index_2730_; 
lean_inc_ref(v_decl_2716_);
v___x_2729_ = l_Lean_PersistentHashMap_insert___at___00Lean_LocalContext_mkLocalDecl_spec__0___redArg(v_fvarIdToDecl_2705_, v___y_2728_, v_decl_2716_);
v_index_2730_ = lean_ctor_get(v_decl_2716_, 0);
lean_inc(v_index_2730_);
v___y_2718_ = v___x_2729_;
v___y_2719_ = v_index_2730_;
goto v___jp_2717_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lean_local_ctx_num_indices(lean_object* v_lctx_2737_){
_start:
{
lean_object* v_decls_2738_; lean_object* v_size_2739_; 
v_decls_2738_ = lean_ctor_get(v_lctx_2737_, 1);
lean_inc_ref(v_decls_2738_);
lean_dec_ref(v_lctx_2737_);
v_size_2739_ = lean_ctor_get(v_decls_2738_, 2);
lean_inc(v_size_2739_);
lean_dec_ref(v_decls_2738_);
return v_size_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f(lean_object* v_lctx_2740_, lean_object* v_i_2741_){
_start:
{
lean_object* v_decls_2742_; lean_object* v_size_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v_decls_2742_ = lean_ctor_get(v_lctx_2740_, 1);
v_size_2743_ = lean_ctor_get(v_decls_2742_, 2);
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_nat_dec_lt(v_i_2741_, v_size_2743_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; 
v___x_2746_ = l_outOfBounds___redArg(v___x_2744_);
return v___x_2746_;
}
else
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2744_, v_decls_2742_, v_i_2741_);
return v___x_2747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getAt_x3f___boxed(lean_object* v_lctx_2748_, lean_object* v_i_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_LocalContext_getAt_x3f(v_lctx_2748_, v_i_2749_);
lean_dec(v_i_2749_);
lean_dec_ref(v_lctx_2748_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___lam__0(lean_object* v_toPure_2751_, lean_object* v_f_2752_, lean_object* v_b_2753_, lean_object* v_decl_2754_){
_start:
{
if (lean_obj_tag(v_decl_2754_) == 0)
{
lean_object* v___x_2755_; 
lean_dec(v_f_2752_);
v___x_2755_ = lean_apply_2(v_toPure_2751_, lean_box(0), v_b_2753_);
return v___x_2755_;
}
else
{
lean_object* v_val_2756_; lean_object* v___x_2757_; 
lean_dec(v_toPure_2751_);
v_val_2756_ = lean_ctor_get(v_decl_2754_, 0);
lean_inc(v_val_2756_);
lean_dec_ref_known(v_decl_2754_, 1);
v___x_2757_ = lean_apply_2(v_f_2752_, v_b_2753_, v_val_2756_);
return v___x_2757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg(lean_object* v_inst_2758_, lean_object* v_lctx_2759_, lean_object* v_f_2760_, lean_object* v_init_2761_, lean_object* v_start_2762_){
_start:
{
lean_object* v_toApplicative_2763_; lean_object* v_decls_2764_; lean_object* v_toPure_2765_; lean_object* v___f_2766_; lean_object* v___x_2767_; 
v_toApplicative_2763_ = lean_ctor_get(v_inst_2758_, 0);
v_decls_2764_ = lean_ctor_get(v_lctx_2759_, 1);
lean_inc_ref(v_decls_2764_);
lean_dec_ref(v_lctx_2759_);
v_toPure_2765_ = lean_ctor_get(v_toApplicative_2763_, 1);
lean_inc(v_toPure_2765_);
v___f_2766_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2766_, 0, v_toPure_2765_);
lean_closure_set(v___f_2766_, 1, v_f_2760_);
v___x_2767_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_2758_, v_decls_2764_, v___f_2766_, v_init_2761_, v_start_2762_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___redArg___boxed(lean_object* v_inst_2768_, lean_object* v_lctx_2769_, lean_object* v_f_2770_, lean_object* v_init_2771_, lean_object* v_start_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2768_, v_lctx_2769_, v_f_2770_, v_init_2771_, v_start_2772_);
lean_dec(v_start_2772_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM(lean_object* v_m_2774_, lean_object* v_00_u03b2_2775_, lean_object* v_inst_2776_, lean_object* v_lctx_2777_, lean_object* v_f_2778_, lean_object* v_init_2779_, lean_object* v_start_2780_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Lean_LocalContext_foldlM___redArg(v_inst_2776_, v_lctx_2777_, v_f_2778_, v_init_2779_, v_start_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___boxed(lean_object* v_m_2782_, lean_object* v_00_u03b2_2783_, lean_object* v_inst_2784_, lean_object* v_lctx_2785_, lean_object* v_f_2786_, lean_object* v_init_2787_, lean_object* v_start_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_LocalContext_foldlM(v_m_2782_, v_00_u03b2_2783_, v_inst_2784_, v_lctx_2785_, v_f_2786_, v_init_2787_, v_start_2788_);
lean_dec(v_start_2788_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg___lam__0(lean_object* v_toPure_2790_, lean_object* v_f_2791_, lean_object* v_decl_2792_, lean_object* v_b_2793_){
_start:
{
if (lean_obj_tag(v_decl_2792_) == 0)
{
lean_object* v___x_2794_; 
lean_dec(v_f_2791_);
v___x_2794_ = lean_apply_2(v_toPure_2790_, lean_box(0), v_b_2793_);
return v___x_2794_;
}
else
{
lean_object* v_val_2795_; lean_object* v___x_2796_; 
lean_dec(v_toPure_2790_);
v_val_2795_ = lean_ctor_get(v_decl_2792_, 0);
lean_inc(v_val_2795_);
lean_dec_ref_known(v_decl_2792_, 1);
v___x_2796_ = lean_apply_2(v_f_2791_, v_val_2795_, v_b_2793_);
return v___x_2796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___redArg(lean_object* v_inst_2797_, lean_object* v_lctx_2798_, lean_object* v_f_2799_, lean_object* v_init_2800_){
_start:
{
lean_object* v_toApplicative_2801_; lean_object* v_decls_2802_; lean_object* v_toPure_2803_; lean_object* v___f_2804_; lean_object* v___x_2805_; 
v_toApplicative_2801_ = lean_ctor_get(v_inst_2797_, 0);
v_decls_2802_ = lean_ctor_get(v_lctx_2798_, 1);
lean_inc_ref(v_decls_2802_);
lean_dec_ref(v_lctx_2798_);
v_toPure_2803_ = lean_ctor_get(v_toApplicative_2801_, 1);
lean_inc(v_toPure_2803_);
v___f_2804_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldrM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2804_, 0, v_toPure_2803_);
lean_closure_set(v___f_2804_, 1, v_f_2799_);
v___x_2805_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_2797_, v_decls_2802_, v___f_2804_, v_init_2800_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM(lean_object* v_m_2806_, lean_object* v_00_u03b2_2807_, lean_object* v_inst_2808_, lean_object* v_lctx_2809_, lean_object* v_f_2810_, lean_object* v_init_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_LocalContext_foldrM___redArg(v_inst_2808_, v_lctx_2809_, v_f_2810_, v_init_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___lam__0(lean_object* v_toPure_2813_, lean_object* v_f_2814_, lean_object* v_decl_2815_){
_start:
{
if (lean_obj_tag(v_decl_2815_) == 0)
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
lean_dec(v_f_2814_);
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_apply_2(v_toPure_2813_, lean_box(0), v___x_2816_);
return v___x_2817_;
}
else
{
lean_object* v_val_2818_; lean_object* v___x_2819_; 
lean_dec(v_toPure_2813_);
v_val_2818_ = lean_ctor_get(v_decl_2815_, 0);
lean_inc(v_val_2818_);
lean_dec_ref_known(v_decl_2815_, 1);
v___x_2819_ = lean_apply_1(v_f_2814_, v_val_2818_);
return v___x_2819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg(lean_object* v_inst_2820_, lean_object* v_lctx_2821_, lean_object* v_f_2822_, lean_object* v_start_2823_){
_start:
{
lean_object* v_toApplicative_2824_; lean_object* v_decls_2825_; lean_object* v_toPure_2826_; lean_object* v___f_2827_; lean_object* v___x_2828_; 
v_toApplicative_2824_ = lean_ctor_get(v_inst_2820_, 0);
v_decls_2825_ = lean_ctor_get(v_lctx_2821_, 1);
lean_inc_ref(v_decls_2825_);
lean_dec_ref(v_lctx_2821_);
v_toPure_2826_ = lean_ctor_get(v_toApplicative_2824_, 1);
lean_inc(v_toPure_2826_);
v___f_2827_ = lean_alloc_closure((void*)(l_Lean_LocalContext_forM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2827_, 0, v_toPure_2826_);
lean_closure_set(v___f_2827_, 1, v_f_2822_);
v___x_2828_ = l_Lean_PersistentArray_forM___redArg(v_inst_2820_, v_decls_2825_, v___f_2827_, v_start_2823_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___redArg___boxed(lean_object* v_inst_2829_, lean_object* v_lctx_2830_, lean_object* v_f_2831_, lean_object* v_start_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_LocalContext_forM___redArg(v_inst_2829_, v_lctx_2830_, v_f_2831_, v_start_2832_);
lean_dec(v_start_2832_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM(lean_object* v_m_2834_, lean_object* v_inst_2835_, lean_object* v_lctx_2836_, lean_object* v_f_2837_, lean_object* v_start_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_LocalContext_forM___redArg(v_inst_2835_, v_lctx_2836_, v_f_2837_, v_start_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_forM___boxed(lean_object* v_m_2840_, lean_object* v_inst_2841_, lean_object* v_lctx_2842_, lean_object* v_f_2843_, lean_object* v_start_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Lean_LocalContext_forM(v_m_2840_, v_inst_2841_, v_lctx_2842_, v_f_2843_, v_start_2844_);
lean_dec(v_start_2844_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0(lean_object* v_toPure_2846_, lean_object* v_f_2847_, lean_object* v_decl_2848_){
_start:
{
if (lean_obj_tag(v_decl_2848_) == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_dec(v_f_2847_);
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_apply_2(v_toPure_2846_, lean_box(0), v___x_2849_);
return v___x_2850_;
}
else
{
lean_object* v_val_2851_; lean_object* v___x_2852_; 
lean_dec(v_toPure_2846_);
v_val_2851_ = lean_ctor_get(v_decl_2848_, 0);
lean_inc(v_val_2851_);
lean_dec_ref_known(v_decl_2848_, 1);
v___x_2852_ = lean_apply_1(v_f_2847_, v_val_2851_);
return v___x_2852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___redArg(lean_object* v_inst_2853_, lean_object* v_lctx_2854_, lean_object* v_f_2855_){
_start:
{
lean_object* v_toApplicative_2856_; lean_object* v_decls_2857_; lean_object* v_toPure_2858_; lean_object* v___f_2859_; lean_object* v___x_2860_; 
v_toApplicative_2856_ = lean_ctor_get(v_inst_2853_, 0);
v_decls_2857_ = lean_ctor_get(v_lctx_2854_, 1);
lean_inc_ref(v_decls_2857_);
lean_dec_ref(v_lctx_2854_);
v_toPure_2858_ = lean_ctor_get(v_toApplicative_2856_, 1);
lean_inc(v_toPure_2858_);
v___f_2859_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2859_, 0, v_toPure_2858_);
lean_closure_set(v___f_2859_, 1, v_f_2855_);
v___x_2860_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_2853_, v_decls_2857_, v___f_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f(lean_object* v_m_2861_, lean_object* v_00_u03b2_2862_, lean_object* v_inst_2863_, lean_object* v_lctx_2864_, lean_object* v_f_2865_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v_inst_2863_, v_lctx_2864_, v_f_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___redArg(lean_object* v_inst_2867_, lean_object* v_lctx_2868_, lean_object* v_f_2869_){
_start:
{
lean_object* v_toApplicative_2870_; lean_object* v_decls_2871_; lean_object* v_toPure_2872_; lean_object* v___f_2873_; lean_object* v___x_2874_; 
v_toApplicative_2870_ = lean_ctor_get(v_inst_2867_, 0);
v_decls_2871_ = lean_ctor_get(v_lctx_2868_, 1);
lean_inc_ref(v_decls_2871_);
lean_dec_ref(v_lctx_2868_);
v_toPure_2872_ = lean_ctor_get(v_toApplicative_2870_, 1);
lean_inc(v_toPure_2872_);
v___f_2873_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDeclM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2873_, 0, v_toPure_2872_);
lean_closure_set(v___f_2873_, 1, v_f_2869_);
v___x_2874_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_2867_, v_decls_2871_, v___f_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f(lean_object* v_m_2875_, lean_object* v_00_u03b2_2876_, lean_object* v_inst_2877_, lean_object* v_lctx_2878_, lean_object* v_f_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v_inst_2877_, v_lctx_2878_, v_f_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0(lean_object* v_toPure_2881_, lean_object* v_f_2882_, lean_object* v_d_x3f_2883_, lean_object* v_b_2884_){
_start:
{
if (lean_obj_tag(v_d_x3f_2883_) == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec(v_f_2882_);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_b_2884_);
v___x_2886_ = lean_apply_2(v_toPure_2881_, lean_box(0), v___x_2885_);
return v___x_2886_;
}
else
{
lean_object* v_val_2887_; lean_object* v___x_2888_; 
lean_dec(v_toPure_2881_);
v_val_2887_ = lean_ctor_get(v_d_x3f_2883_, 0);
lean_inc(v_val_2887_);
lean_dec_ref_known(v_d_x3f_2883_, 1);
v___x_2888_ = lean_apply_2(v_f_2882_, v_val_2887_, v_b_2884_);
return v___x_2888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(lean_object* v_toPure_2889_, lean_object* v_inst_2890_, lean_object* v_00_u03b2_2891_, lean_object* v_lctx_2892_, lean_object* v_init_2893_, lean_object* v_f_2894_){
_start:
{
lean_object* v_decls_2895_; lean_object* v___f_2896_; lean_object* v___x_2897_; 
v_decls_2895_ = lean_ctor_get(v_lctx_2892_, 1);
v___f_2896_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2896_, 0, v_toPure_2889_);
lean_closure_set(v___f_2896_, 1, v_f_2894_);
v___x_2897_ = l_Lean_PersistentArray_forIn___redArg(v_inst_2890_, v_decls_2895_, v_init_2893_, v___f_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed(lean_object* v_toPure_2898_, lean_object* v_inst_2899_, lean_object* v_00_u03b2_2900_, lean_object* v_lctx_2901_, lean_object* v_init_2902_, lean_object* v_f_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1(v_toPure_2898_, v_inst_2899_, v_00_u03b2_2900_, v_lctx_2901_, v_init_2902_, v_f_2903_);
lean_dec_ref(v_lctx_2901_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(lean_object* v_inst_2905_){
_start:
{
lean_object* v_toApplicative_2906_; lean_object* v_toPure_2907_; lean_object* v___f_2908_; 
v_toApplicative_2906_ = lean_ctor_get(v_inst_2905_, 0);
v_toPure_2907_ = lean_ctor_get(v_toApplicative_2906_, 1);
lean_inc(v_toPure_2907_);
v___f_2908_ = lean_alloc_closure((void*)(l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_2908_, 0, v_toPure_2907_);
lean_closure_set(v___f_2908_, 1, v_inst_2905_);
return v___f_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_instForInLocalDeclOfMonad(lean_object* v_m_2909_, lean_object* v_inst_2910_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_LocalContext_instForInLocalDeclOfMonad___redArg(v_inst_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___lam__0(lean_object* v_f_2912_, lean_object* v_x1_2913_, lean_object* v_x2_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = lean_apply_2(v_f_2912_, v_x1_2913_, v_x2_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg(lean_object* v_lctx_2935_, lean_object* v_f_2936_, lean_object* v_init_2937_, lean_object* v_start_2938_){
_start:
{
lean_object* v___f_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___f_2939_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2939_, 0, v_f_2936_);
v___x_2940_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2941_ = l_Lean_LocalContext_foldlM___redArg(v___x_2940_, v_lctx_2935_, v___f_2939_, v_init_2937_, v_start_2938_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___redArg___boxed(lean_object* v_lctx_2942_, lean_object* v_f_2943_, lean_object* v_init_2944_, lean_object* v_start_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_LocalContext_foldl___redArg(v_lctx_2942_, v_f_2943_, v_init_2944_, v_start_2945_);
lean_dec(v_start_2945_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl(lean_object* v_00_u03b2_2947_, lean_object* v_lctx_2948_, lean_object* v_f_2949_, lean_object* v_init_2950_, lean_object* v_start_2951_){
_start:
{
lean_object* v___f_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___f_2952_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2952_, 0, v_f_2949_);
v___x_2953_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2954_ = l_Lean_LocalContext_foldlM___redArg(v___x_2953_, v_lctx_2948_, v___f_2952_, v_init_2950_, v_start_2951_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldl___boxed(lean_object* v_00_u03b2_2955_, lean_object* v_lctx_2956_, lean_object* v_f_2957_, lean_object* v_init_2958_, lean_object* v_start_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_LocalContext_foldl(v_00_u03b2_2955_, v_lctx_2956_, v_f_2957_, v_init_2958_, v_start_2959_);
lean_dec(v_start_2959_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg___lam__0(lean_object* v_f_2961_, lean_object* v_x1_2962_, lean_object* v_x2_2963_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_apply_2(v_f_2961_, v_x1_2962_, v_x2_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr___redArg(lean_object* v_lctx_2965_, lean_object* v_f_2966_, lean_object* v_init_2967_){
_start:
{
lean_object* v___f_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___f_2968_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2968_, 0, v_f_2966_);
v___x_2969_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2970_ = l_Lean_LocalContext_foldrM___redArg(v___x_2969_, v_lctx_2965_, v___f_2968_, v_init_2967_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldr(lean_object* v_00_u03b2_2971_, lean_object* v_lctx_2972_, lean_object* v_f_2973_, lean_object* v_init_2974_){
_start:
{
lean_object* v___f_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___f_2975_ = lean_alloc_closure((void*)(l_Lean_LocalContext_foldr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2975_, 0, v_f_2973_);
v___x_2976_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_2977_ = l_Lean_LocalContext_foldrM___redArg(v___x_2976_, v_lctx_2972_, v___f_2975_, v_init_2974_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(lean_object* v_as_2978_, size_t v_i_2979_, size_t v_stop_2980_, lean_object* v_b_2981_){
_start:
{
lean_object* v___y_2983_; uint8_t v___x_2987_; 
v___x_2987_ = lean_usize_dec_eq(v_i_2979_, v_stop_2980_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_array_uget_borrowed(v_as_2978_, v_i_2979_);
if (lean_obj_tag(v___x_2988_) == 0)
{
v___y_2983_ = v_b_2981_;
goto v___jp_2982_;
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_unsigned_to_nat(1u);
v___x_2990_ = lean_nat_add(v_b_2981_, v___x_2989_);
lean_dec(v_b_2981_);
v___y_2983_ = v___x_2990_;
goto v___jp_2982_;
}
}
else
{
return v_b_2981_;
}
v___jp_2982_:
{
size_t v___x_2984_; size_t v___x_2985_; 
v___x_2984_ = ((size_t)1ULL);
v___x_2985_ = lean_usize_add(v_i_2979_, v___x_2984_);
v_i_2979_ = v___x_2985_;
v_b_2981_ = v___y_2983_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2___boxed(lean_object* v_as_2991_, lean_object* v_i_2992_, lean_object* v_stop_2993_, lean_object* v_b_2994_){
_start:
{
size_t v_i_boxed_2995_; size_t v_stop_boxed_2996_; lean_object* v_res_2997_; 
v_i_boxed_2995_ = lean_unbox_usize(v_i_2992_);
lean_dec(v_i_2992_);
v_stop_boxed_2996_ = lean_unbox_usize(v_stop_2993_);
lean_dec(v_stop_2993_);
v_res_2997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_as_2991_, v_i_boxed_2995_, v_stop_boxed_2996_, v_b_2994_);
lean_dec_ref(v_as_2991_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(lean_object* v_x_2998_, lean_object* v_x_2999_){
_start:
{
if (lean_obj_tag(v_x_2998_) == 0)
{
lean_object* v_cs_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v_cs_3000_ = lean_ctor_get(v_x_2998_, 0);
v___x_3001_ = lean_unsigned_to_nat(0u);
v___x_3002_ = lean_array_get_size(v_cs_3000_);
v___x_3003_ = lean_nat_dec_lt(v___x_3001_, v___x_3002_);
if (v___x_3003_ == 0)
{
return v_x_2999_;
}
else
{
size_t v___x_3004_; size_t v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = ((size_t)0ULL);
v___x_3005_ = lean_usize_of_nat(v___x_3002_);
v___x_3006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3000_, v___x_3004_, v___x_3005_, v_x_2999_);
return v___x_3006_;
}
}
else
{
lean_object* v_vs_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v_vs_3007_ = lean_ctor_get(v_x_2998_, 0);
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = lean_array_get_size(v_vs_3007_);
v___x_3010_ = lean_nat_dec_lt(v___x_3008_, v___x_3009_);
if (v___x_3010_ == 0)
{
return v_x_2999_;
}
else
{
size_t v___x_3011_; size_t v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = ((size_t)0ULL);
v___x_3012_ = lean_usize_of_nat(v___x_3009_);
v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3007_, v___x_3011_, v___x_3012_, v_x_2999_);
return v___x_3013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_3014_, size_t v_i_3015_, size_t v_stop_3016_, lean_object* v_b_3017_){
_start:
{
uint8_t v___x_3018_; 
v___x_3018_ = lean_usize_dec_eq(v_i_3015_, v_stop_3016_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; size_t v___x_3021_; size_t v___x_3022_; 
v___x_3019_ = lean_array_uget_borrowed(v_as_3014_, v_i_3015_);
v___x_3020_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v___x_3019_, v_b_3017_);
v___x_3021_ = ((size_t)1ULL);
v___x_3022_ = lean_usize_add(v_i_3015_, v___x_3021_);
v_i_3015_ = v___x_3022_;
v_b_3017_ = v___x_3020_;
goto _start;
}
else
{
return v_b_3017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3024_, lean_object* v_i_3025_, lean_object* v_stop_3026_, lean_object* v_b_3027_){
_start:
{
size_t v_i_boxed_3028_; size_t v_stop_boxed_3029_; lean_object* v_res_3030_; 
v_i_boxed_3028_ = lean_unbox_usize(v_i_3025_);
lean_dec(v_i_3025_);
v_stop_boxed_3029_ = lean_unbox_usize(v_stop_3026_);
lean_dec(v_stop_3026_);
v_res_3030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_as_3024_, v_i_boxed_3028_, v_stop_boxed_3029_, v_b_3027_);
lean_dec_ref(v_as_3024_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3___boxed(lean_object* v_x_3031_, lean_object* v_x_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_x_3031_, v_x_3032_);
lean_dec_ref(v_x_3031_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(lean_object* v_x_3034_, size_t v_x_3035_, size_t v_x_3036_, lean_object* v_x_3037_){
_start:
{
if (lean_obj_tag(v_x_3034_) == 0)
{
lean_object* v_cs_3038_; lean_object* v___x_3039_; size_t v___x_3040_; lean_object* v_j_3041_; lean_object* v___x_3042_; size_t v___x_3043_; size_t v___x_3044_; size_t v___x_3045_; size_t v___x_3046_; size_t v___x_3047_; size_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; 
v_cs_3038_ = lean_ctor_get(v_x_3034_, 0);
v___x_3039_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_getFVarIds_spec__0_spec__0___closed__0);
v___x_3040_ = lean_usize_shift_right(v_x_3035_, v_x_3036_);
v_j_3041_ = lean_usize_to_nat(v___x_3040_);
v___x_3042_ = lean_array_get_borrowed(v___x_3039_, v_cs_3038_, v_j_3041_);
v___x_3043_ = ((size_t)1ULL);
v___x_3044_ = lean_usize_shift_left(v___x_3043_, v_x_3036_);
v___x_3045_ = lean_usize_sub(v___x_3044_, v___x_3043_);
v___x_3046_ = lean_usize_land(v_x_3035_, v___x_3045_);
v___x_3047_ = ((size_t)5ULL);
v___x_3048_ = lean_usize_sub(v_x_3036_, v___x_3047_);
v___x_3049_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v___x_3042_, v___x_3046_, v___x_3048_, v_x_3037_);
v___x_3050_ = lean_unsigned_to_nat(1u);
v___x_3051_ = lean_nat_add(v_j_3041_, v___x_3050_);
lean_dec(v_j_3041_);
v___x_3052_ = lean_array_get_size(v_cs_3038_);
v___x_3053_ = lean_nat_dec_lt(v___x_3051_, v___x_3052_);
if (v___x_3053_ == 0)
{
lean_dec(v___x_3051_);
return v___x_3049_;
}
else
{
size_t v___x_3054_; size_t v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = lean_usize_of_nat(v___x_3051_);
lean_dec(v___x_3051_);
v___x_3055_ = lean_usize_of_nat(v___x_3052_);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1_spec__2(v_cs_3038_, v___x_3054_, v___x_3055_, v___x_3049_);
return v___x_3056_;
}
}
else
{
lean_object* v_vs_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v_vs_3057_ = lean_ctor_get(v_x_3034_, 0);
v___x_3058_ = lean_usize_to_nat(v_x_3035_);
v___x_3059_ = lean_array_get_size(v_vs_3057_);
v___x_3060_ = lean_nat_dec_lt(v___x_3058_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_dec(v___x_3058_);
return v_x_3037_;
}
else
{
size_t v___x_3061_; size_t v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = lean_usize_of_nat(v___x_3058_);
lean_dec(v___x_3058_);
v___x_3062_ = lean_usize_of_nat(v___x_3059_);
v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_vs_3057_, v___x_3061_, v___x_3062_, v_x_3037_);
return v___x_3063_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3064_, lean_object* v_x_3065_, lean_object* v_x_3066_, lean_object* v_x_3067_){
_start:
{
size_t v_x_1185__boxed_3068_; size_t v_x_1186__boxed_3069_; lean_object* v_res_3070_; 
v_x_1185__boxed_3068_ = lean_unbox_usize(v_x_3065_);
lean_dec(v_x_3065_);
v_x_1186__boxed_3069_ = lean_unbox_usize(v_x_3066_);
lean_dec(v_x_3066_);
v_res_3070_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_x_3064_, v_x_1185__boxed_3068_, v_x_1186__boxed_3069_, v_x_3067_);
lean_dec_ref(v_x_3064_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(lean_object* v_t_3071_, lean_object* v_init_3072_, lean_object* v_start_3073_){
_start:
{
lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_3074_ = lean_unsigned_to_nat(0u);
v___x_3075_ = lean_nat_dec_eq(v_start_3073_, v___x_3074_);
if (v___x_3075_ == 0)
{
lean_object* v_root_3076_; lean_object* v_tail_3077_; size_t v_shift_3078_; lean_object* v_tailOff_3079_; uint8_t v___x_3080_; 
v_root_3076_ = lean_ctor_get(v_t_3071_, 0);
v_tail_3077_ = lean_ctor_get(v_t_3071_, 1);
v_shift_3078_ = lean_ctor_get_usize(v_t_3071_, 4);
v_tailOff_3079_ = lean_ctor_get(v_t_3071_, 3);
v___x_3080_ = lean_nat_dec_le(v_tailOff_3079_, v_start_3073_);
if (v___x_3080_ == 0)
{
size_t v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3081_ = lean_usize_of_nat(v_start_3073_);
v___x_3082_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__1(v_root_3076_, v___x_3081_, v_shift_3078_, v_init_3072_);
v___x_3083_ = lean_array_get_size(v_tail_3077_);
v___x_3084_ = lean_nat_dec_lt(v___x_3074_, v___x_3083_);
if (v___x_3084_ == 0)
{
return v___x_3082_;
}
else
{
size_t v___x_3085_; size_t v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = ((size_t)0ULL);
v___x_3086_ = lean_usize_of_nat(v___x_3083_);
v___x_3087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3077_, v___x_3085_, v___x_3086_, v___x_3082_);
return v___x_3087_;
}
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; 
v___x_3088_ = lean_nat_sub(v_start_3073_, v_tailOff_3079_);
v___x_3089_ = lean_array_get_size(v_tail_3077_);
v___x_3090_ = lean_nat_dec_lt(v___x_3088_, v___x_3089_);
if (v___x_3090_ == 0)
{
lean_dec(v___x_3088_);
return v_init_3072_;
}
else
{
size_t v___x_3091_; size_t v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = lean_usize_of_nat(v___x_3088_);
lean_dec(v___x_3088_);
v___x_3092_ = lean_usize_of_nat(v___x_3089_);
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3077_, v___x_3091_, v___x_3092_, v_init_3072_);
return v___x_3093_;
}
}
}
else
{
lean_object* v_root_3094_; lean_object* v_tail_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v_root_3094_ = lean_ctor_get(v_t_3071_, 0);
v_tail_3095_ = lean_ctor_get(v_t_3071_, 1);
v___x_3096_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__3(v_root_3094_, v_init_3072_);
v___x_3097_ = lean_array_get_size(v_tail_3095_);
v___x_3098_ = lean_nat_dec_lt(v___x_3074_, v___x_3097_);
if (v___x_3098_ == 0)
{
return v___x_3096_;
}
else
{
size_t v___x_3099_; size_t v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = ((size_t)0ULL);
v___x_3100_ = lean_usize_of_nat(v___x_3097_);
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0_spec__2(v_tail_3095_, v___x_3099_, v___x_3100_, v___x_3096_);
return v___x_3101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0___boxed(lean_object* v_t_3102_, lean_object* v_init_3103_, lean_object* v_start_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_t_3102_, v_init_3103_, v_start_3104_);
lean_dec(v_start_3104_);
lean_dec_ref(v_t_3102_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(lean_object* v_lctx_3106_, lean_object* v_init_3107_, lean_object* v_start_3108_){
_start:
{
lean_object* v_decls_3109_; lean_object* v___x_3110_; 
v_decls_3109_ = lean_ctor_get(v_lctx_3106_, 1);
v___x_3110_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0_spec__0(v_decls_3109_, v_init_3107_, v_start_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0___boxed(lean_object* v_lctx_3111_, lean_object* v_init_3112_, lean_object* v_start_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3111_, v_init_3112_, v_start_3113_);
lean_dec(v_start_3113_);
lean_dec_ref(v_lctx_3111_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size(lean_object* v_lctx_3115_){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = l_Lean_LocalContext_foldlM___at___00Lean_LocalContext_size_spec__0(v_lctx_3115_, v___x_3116_, v___x_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_size___boxed(lean_object* v_lctx_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_LocalContext_size(v_lctx_3118_);
lean_dec_ref(v_lctx_3118_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg___lam__0(lean_object* v_f_3120_, lean_object* v_x_3121_){
_start:
{
lean_object* v___x_3122_; 
v___x_3122_ = lean_apply_1(v_f_3120_, v_x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f___redArg(lean_object* v_lctx_3123_, lean_object* v_f_3124_){
_start:
{
lean_object* v___f_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___f_3125_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3125_, 0, v_f_3124_);
v___x_3126_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3127_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3126_, v_lctx_3123_, v___f_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDecl_x3f(lean_object* v_00_u03b2_3128_, lean_object* v_lctx_3129_, lean_object* v_f_3130_){
_start:
{
lean_object* v___f_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___f_3131_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3131_, 0, v_f_3130_);
v___x_3132_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3133_ = l_Lean_LocalContext_findDeclM_x3f___redArg(v___x_3132_, v_lctx_3129_, v___f_3131_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f___redArg(lean_object* v_lctx_3134_, lean_object* v_f_3135_){
_start:
{
lean_object* v___f_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___f_3136_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3136_, 0, v_f_3135_);
v___x_3137_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3138_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3137_, v_lctx_3134_, v___f_3136_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRev_x3f(lean_object* v_00_u03b2_3139_, lean_object* v_lctx_3140_, lean_object* v_f_3141_){
_start:
{
lean_object* v___f_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___f_3142_ = lean_alloc_closure((void*)(l_Lean_LocalContext_findDecl_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3142_, 0, v_f_3141_);
v___x_3143_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v___x_3144_ = l_Lean_LocalContext_findDeclRevM_x3f___redArg(v___x_3143_, v_lctx_3140_, v___f_3142_);
return v___x_3144_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(lean_object* v_val_3145_, lean_object* v_as_3146_, size_t v_i_3147_, size_t v_stop_3148_){
_start:
{
uint8_t v___x_3149_; 
v___x_3149_ = lean_usize_dec_eq(v_i_3147_, v_stop_3148_);
if (v___x_3149_ == 0)
{
uint8_t v___x_3150_; uint8_t v___y_3152_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v_fvarId_3158_; uint8_t v___x_3159_; 
v___x_3150_ = 1;
v___x_3156_ = lean_array_uget_borrowed(v_as_3146_, v_i_3147_);
v___x_3157_ = l_Lean_Expr_fvarId_x21(v___x_3156_);
v_fvarId_3158_ = lean_ctor_get(v_val_3145_, 1);
v___x_3159_ = l_Lean_instBEqFVarId_beq(v___x_3157_, v_fvarId_3158_);
lean_dec(v___x_3157_);
v___y_3152_ = v___x_3159_;
goto v___jp_3151_;
v___jp_3151_:
{
if (v___y_3152_ == 0)
{
size_t v___x_3153_; size_t v___x_3154_; 
v___x_3153_ = ((size_t)1ULL);
v___x_3154_ = lean_usize_add(v_i_3147_, v___x_3153_);
v_i_3147_ = v___x_3154_;
goto _start;
}
else
{
return v___x_3150_;
}
}
}
else
{
uint8_t v___x_3160_; 
v___x_3160_ = 0;
return v___x_3160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0___boxed(lean_object* v_val_3161_, lean_object* v_as_3162_, lean_object* v_i_3163_, lean_object* v_stop_3164_){
_start:
{
size_t v_i_boxed_3165_; size_t v_stop_boxed_3166_; uint8_t v_res_3167_; lean_object* v_r_3168_; 
v_i_boxed_3165_ = lean_unbox_usize(v_i_3163_);
lean_dec(v_i_3163_);
v_stop_boxed_3166_ = lean_unbox_usize(v_stop_3164_);
lean_dec(v_stop_3164_);
v_res_3167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3161_, v_as_3162_, v_i_boxed_3165_, v_stop_boxed_3166_);
lean_dec_ref(v_as_3162_);
lean_dec_ref(v_val_3161_);
v_r_3168_ = lean_box(v_res_3167_);
return v_r_3168_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOfAux(lean_object* v_a_u2081_3169_, lean_object* v_a_u2082_3170_, lean_object* v_exceptFVars_3171_, lean_object* v_i_3172_, lean_object* v_j_3173_){
_start:
{
lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v_size_3189_; uint8_t v___x_3190_; 
v_size_3189_ = lean_ctor_get(v_a_u2081_3169_, 2);
v___x_3190_ = lean_nat_dec_lt(v_i_3172_, v_size_3189_);
if (v___x_3190_ == 0)
{
uint8_t v___x_3191_; 
lean_dec(v_j_3173_);
lean_dec(v_i_3172_);
v___x_3191_ = 1;
return v___x_3191_;
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = lean_box(0);
v___x_3193_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3192_, v_a_u2081_3169_, v_i_3172_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = lean_unsigned_to_nat(1u);
v___x_3195_ = lean_nat_add(v_i_3172_, v___x_3194_);
lean_dec(v_i_3172_);
v_i_3172_ = v___x_3195_;
goto _start;
}
else
{
lean_object* v_val_3197_; lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v_val_3197_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_val_3197_);
lean_dec_ref_known(v___x_3193_, 1);
v___x_3207_ = lean_unsigned_to_nat(0u);
v___x_3208_ = lean_array_get_size(v_exceptFVars_3171_);
v___x_3209_ = lean_nat_dec_lt(v___x_3207_, v___x_3208_);
if (v___x_3209_ == 0)
{
goto v___jp_3198_;
}
else
{
if (v___x_3209_ == 0)
{
goto v___jp_3198_;
}
else
{
size_t v___x_3210_; size_t v___x_3211_; uint8_t v___x_3212_; 
v___x_3210_ = ((size_t)0ULL);
v___x_3211_ = lean_usize_of_nat(v___x_3208_);
v___x_3212_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LocalContext_isSubPrefixOfAux_spec__0(v_val_3197_, v_exceptFVars_3171_, v___x_3210_, v___x_3211_);
if (v___x_3212_ == 0)
{
goto v___jp_3198_;
}
else
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
lean_dec(v_val_3197_);
v___x_3213_ = lean_unsigned_to_nat(1u);
v___x_3214_ = lean_nat_add(v_i_3172_, v___x_3213_);
lean_dec(v_i_3172_);
v_i_3172_ = v___x_3214_;
goto _start;
}
}
}
v___jp_3198_:
{
lean_object* v_size_3199_; uint8_t v___x_3200_; 
v_size_3199_ = lean_ctor_get(v_a_u2082_3170_, 2);
v___x_3200_ = lean_nat_dec_lt(v_j_3173_, v_size_3199_);
if (v___x_3200_ == 0)
{
lean_dec(v_val_3197_);
lean_dec(v_j_3173_);
lean_dec(v_i_3172_);
return v___x_3200_;
}
else
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3192_, v_a_u2082_3170_, v_j_3173_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
lean_dec(v_val_3197_);
v___x_3202_ = lean_unsigned_to_nat(1u);
v___x_3203_ = lean_nat_add(v_j_3173_, v___x_3202_);
lean_dec(v_j_3173_);
v_j_3173_ = v___x_3203_;
goto _start;
}
else
{
lean_object* v_val_3205_; lean_object* v_fvarId_3206_; 
v_val_3205_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_val_3205_);
lean_dec_ref_known(v___x_3201_, 1);
v_fvarId_3206_ = lean_ctor_get(v_val_3197_, 1);
lean_inc(v_fvarId_3206_);
lean_dec(v_val_3197_);
v___y_3186_ = v_val_3205_;
v___y_3187_ = v_fvarId_3206_;
goto v___jp_3185_;
}
}
}
}
}
v___jp_3174_:
{
uint8_t v___x_3177_; 
v___x_3177_ = l_Lean_instBEqFVarId_beq(v___y_3175_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec(v___y_3175_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = lean_unsigned_to_nat(1u);
v___x_3179_ = lean_nat_add(v_j_3173_, v___x_3178_);
lean_dec(v_j_3173_);
v_j_3173_ = v___x_3179_;
goto _start;
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = lean_unsigned_to_nat(1u);
v___x_3182_ = lean_nat_add(v_i_3172_, v___x_3181_);
lean_dec(v_i_3172_);
v___x_3183_ = lean_nat_add(v_j_3173_, v___x_3181_);
lean_dec(v_j_3173_);
v_i_3172_ = v___x_3182_;
v_j_3173_ = v___x_3183_;
goto _start;
}
}
v___jp_3185_:
{
lean_object* v_fvarId_3188_; 
v_fvarId_3188_ = lean_ctor_get(v___y_3186_, 1);
lean_inc(v_fvarId_3188_);
lean_dec_ref(v___y_3186_);
v___y_3175_ = v___y_3187_;
v___y_3176_ = v_fvarId_3188_;
goto v___jp_3174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOfAux___boxed(lean_object* v_a_u2081_3216_, lean_object* v_a_u2082_3217_, lean_object* v_exceptFVars_3218_, lean_object* v_i_3219_, lean_object* v_j_3220_){
_start:
{
uint8_t v_res_3221_; lean_object* v_r_3222_; 
v_res_3221_ = l_Lean_LocalContext_isSubPrefixOfAux(v_a_u2081_3216_, v_a_u2082_3217_, v_exceptFVars_3218_, v_i_3219_, v_j_3220_);
lean_dec_ref(v_exceptFVars_3218_);
lean_dec_ref(v_a_u2082_3217_);
lean_dec_ref(v_a_u2081_3216_);
v_r_3222_ = lean_box(v_res_3221_);
return v_r_3222_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object* v_lctx_u2081_3223_, lean_object* v_lctx_u2082_3224_, lean_object* v_exceptFVars_3225_){
_start:
{
lean_object* v_decls_3226_; lean_object* v_decls_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; 
v_decls_3226_ = lean_ctor_get(v_lctx_u2081_3223_, 1);
v_decls_3227_ = lean_ctor_get(v_lctx_u2082_3224_, 1);
v___x_3228_ = lean_unsigned_to_nat(0u);
v___x_3229_ = l_Lean_LocalContext_isSubPrefixOfAux(v_decls_3226_, v_decls_3227_, v_exceptFVars_3225_, v___x_3228_, v___x_3228_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_isSubPrefixOf___boxed(lean_object* v_lctx_u2081_3230_, lean_object* v_lctx_u2082_3231_, lean_object* v_exceptFVars_3232_){
_start:
{
uint8_t v_res_3233_; lean_object* v_r_3234_; 
v_res_3233_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_u2081_3230_, v_lctx_u2082_3231_, v_exceptFVars_3232_);
lean_dec_ref(v_exceptFVars_3232_);
lean_dec_ref(v_lctx_u2082_3231_);
lean_dec_ref(v_lctx_u2081_3230_);
v_r_3234_ = lean_box(v_res_3233_);
return v_r_3234_;
}
}
static lean_object* _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3236_ = ((lean_object*)(l_Lean_LocalContext_get_x21___closed__1));
v___x_3237_ = lean_unsigned_to_nat(14u);
v___x_3238_ = lean_unsigned_to_nat(576u);
v___x_3239_ = ((lean_object*)(l_Lean_LocalContext_mkBinding___lam__0___closed__0));
v___x_3240_ = ((lean_object*)(l_Lean_LocalDecl_value___closed__0));
v___x_3241_ = l_mkPanicMessageWithDecl(v___x_3240_, v___x_3239_, v___x_3238_, v___x_3237_, v___x_3236_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0(lean_object* v_xs_3242_, lean_object* v_lctx_3243_, lean_object* v___x_3244_, uint8_t v_isLambda_3245_, uint8_t v_usedLetOnly_3246_, uint8_t v_generalizeNondepLet_3247_, lean_object* v_i_3248_, lean_object* v_x_3249_, lean_object* v_b_3250_){
_start:
{
lean_object* v_n_3252_; lean_object* v_ty_3253_; uint8_t v_bi_3254_; lean_object* v_x_3258_; lean_object* v___x_3259_; 
v_x_3258_ = lean_array_fget_borrowed(v_xs_3242_, v_i_3248_);
v___x_3259_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3243_, v_x_3258_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec_ref(v_b_3250_);
v___x_3260_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3261_ = l_panic___redArg(v___x_3244_, v___x_3260_);
return v___x_3261_;
}
else
{
lean_object* v_val_3262_; 
v_val_3262_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_val_3262_);
lean_dec_ref_known(v___x_3259_, 1);
if (lean_obj_tag(v_val_3262_) == 0)
{
lean_object* v_userName_3263_; lean_object* v_type_3264_; uint8_t v_bi_3265_; 
v_userName_3263_ = lean_ctor_get(v_val_3262_, 2);
lean_inc(v_userName_3263_);
v_type_3264_ = lean_ctor_get(v_val_3262_, 3);
lean_inc_ref(v_type_3264_);
v_bi_3265_ = lean_ctor_get_uint8(v_val_3262_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3262_, 4);
v_n_3252_ = v_userName_3263_;
v_ty_3253_ = v_type_3264_;
v_bi_3254_ = v_bi_3265_;
goto v___jp_3251_;
}
else
{
lean_object* v_userName_3266_; lean_object* v_type_3267_; lean_object* v_value_3268_; uint8_t v_nondep_3269_; uint8_t v___y_3275_; 
v_userName_3266_ = lean_ctor_get(v_val_3262_, 2);
lean_inc(v_userName_3266_);
v_type_3267_ = lean_ctor_get(v_val_3262_, 3);
lean_inc_ref(v_type_3267_);
v_value_3268_ = lean_ctor_get(v_val_3262_, 4);
lean_inc_ref(v_value_3268_);
v_nondep_3269_ = lean_ctor_get_uint8(v_val_3262_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3262_, 5);
if (v_nondep_3269_ == 0)
{
v___y_3275_ = v_nondep_3269_;
goto v___jp_3274_;
}
else
{
if (v_generalizeNondepLet_3247_ == 0)
{
v___y_3275_ = v_generalizeNondepLet_3247_;
goto v___jp_3274_;
}
else
{
uint8_t v___x_3280_; 
lean_dec_ref(v_value_3268_);
v___x_3280_ = 0;
v_n_3252_ = v_userName_3266_;
v_ty_3253_ = v_type_3267_;
v_bi_3254_ = v___x_3280_;
goto v___jp_3251_;
}
}
v___jp_3270_:
{
lean_object* v_ty_3271_; lean_object* v_val_3272_; lean_object* v___x_3273_; 
v_ty_3271_ = lean_expr_abstract_range(v_type_3267_, v_i_3248_, v_xs_3242_);
lean_dec_ref(v_type_3267_);
v_val_3272_ = lean_expr_abstract_range(v_value_3268_, v_i_3248_, v_xs_3242_);
lean_dec_ref(v_value_3268_);
v___x_3273_ = l_Lean_Expr_letE___override(v_userName_3266_, v_ty_3271_, v_val_3272_, v_b_3250_, v_nondep_3269_);
return v___x_3273_;
}
v___jp_3274_:
{
if (v_usedLetOnly_3246_ == 0)
{
goto v___jp_3270_;
}
else
{
if (v___y_3275_ == 0)
{
lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3276_ = lean_unsigned_to_nat(0u);
v___x_3277_ = lean_expr_has_loose_bvar(v_b_3250_, v___x_3276_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
lean_dec_ref(v_value_3268_);
lean_dec_ref(v_type_3267_);
lean_dec(v_userName_3266_);
v___x_3278_ = lean_unsigned_to_nat(1u);
v___x_3279_ = lean_expr_lower_loose_bvars(v_b_3250_, v___x_3278_, v___x_3278_);
lean_dec_ref(v_b_3250_);
return v___x_3279_;
}
else
{
goto v___jp_3270_;
}
}
else
{
goto v___jp_3270_;
}
}
}
}
}
v___jp_3251_:
{
lean_object* v_ty_3255_; 
v_ty_3255_ = lean_expr_abstract_range(v_ty_3253_, v_i_3248_, v_xs_3242_);
lean_dec_ref(v_ty_3253_);
if (v_isLambda_3245_ == 0)
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Lean_mkForall(v_n_3252_, v_bi_3254_, v_ty_3255_, v_b_3250_);
return v___x_3256_;
}
else
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_mkLambda(v_n_3252_, v_bi_3254_, v_ty_3255_, v_b_3250_);
return v___x_3257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___lam__0___boxed(lean_object* v_xs_3281_, lean_object* v_lctx_3282_, lean_object* v___x_3283_, lean_object* v_isLambda_3284_, lean_object* v_usedLetOnly_3285_, lean_object* v_generalizeNondepLet_3286_, lean_object* v_i_3287_, lean_object* v_x_3288_, lean_object* v_b_3289_){
_start:
{
uint8_t v_isLambda_boxed_3290_; uint8_t v_usedLetOnly_boxed_3291_; uint8_t v_generalizeNondepLet_boxed_3292_; lean_object* v_res_3293_; 
v_isLambda_boxed_3290_ = lean_unbox(v_isLambda_3284_);
v_usedLetOnly_boxed_3291_ = lean_unbox(v_usedLetOnly_3285_);
v_generalizeNondepLet_boxed_3292_ = lean_unbox(v_generalizeNondepLet_3286_);
v_res_3293_ = l_Lean_LocalContext_mkBinding___lam__0(v_xs_3281_, v_lctx_3282_, v___x_3283_, v_isLambda_boxed_3290_, v_usedLetOnly_boxed_3291_, v_generalizeNondepLet_boxed_3292_, v_i_3287_, v_x_3288_, v_b_3289_);
lean_dec(v_i_3287_);
lean_dec_ref(v___x_3283_);
lean_dec_ref(v_xs_3281_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding(uint8_t v_isLambda_3294_, lean_object* v_lctx_3295_, lean_object* v_xs_3296_, lean_object* v_b_3297_, uint8_t v_usedLetOnly_3298_, uint8_t v_generalizeNondepLet_3299_){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___f_3304_; lean_object* v_b_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3300_ = l_Lean_instInhabitedExpr;
v___x_3301_ = lean_box(v_isLambda_3294_);
v___x_3302_ = lean_box(v_usedLetOnly_3298_);
v___x_3303_ = lean_box(v_generalizeNondepLet_3299_);
lean_inc_ref(v_xs_3296_);
v___f_3304_ = lean_alloc_closure((void*)(l_Lean_LocalContext_mkBinding___lam__0___boxed), 9, 6);
lean_closure_set(v___f_3304_, 0, v_xs_3296_);
lean_closure_set(v___f_3304_, 1, v_lctx_3295_);
lean_closure_set(v___f_3304_, 2, v___x_3300_);
lean_closure_set(v___f_3304_, 3, v___x_3301_);
lean_closure_set(v___f_3304_, 4, v___x_3302_);
lean_closure_set(v___f_3304_, 5, v___x_3303_);
v_b_3305_ = lean_expr_abstract(v_b_3297_, v_xs_3296_);
v___x_3306_ = lean_array_get_size(v_xs_3296_);
lean_dec_ref(v_xs_3296_);
v___x_3307_ = l_Nat_foldRev___redArg(v___x_3306_, v___f_3304_, v_b_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkBinding___boxed(lean_object* v_isLambda_3308_, lean_object* v_lctx_3309_, lean_object* v_xs_3310_, lean_object* v_b_3311_, lean_object* v_usedLetOnly_3312_, lean_object* v_generalizeNondepLet_3313_){
_start:
{
uint8_t v_isLambda_boxed_3314_; uint8_t v_usedLetOnly_boxed_3315_; uint8_t v_generalizeNondepLet_boxed_3316_; lean_object* v_res_3317_; 
v_isLambda_boxed_3314_ = lean_unbox(v_isLambda_3308_);
v_usedLetOnly_boxed_3315_ = lean_unbox(v_usedLetOnly_3312_);
v_generalizeNondepLet_boxed_3316_ = lean_unbox(v_generalizeNondepLet_3313_);
v_res_3317_ = l_Lean_LocalContext_mkBinding(v_isLambda_boxed_3314_, v_lctx_3309_, v_xs_3310_, v_b_3311_, v_usedLetOnly_boxed_3315_, v_generalizeNondepLet_boxed_3316_);
lean_dec_ref(v_b_3311_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(lean_object* v_xs_3318_, lean_object* v_lctx_3319_, uint8_t v_usedLetOnly_3320_, uint8_t v_generalizeNondepLet_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_){
_start:
{
lean_object* v_zero_3324_; uint8_t v_isZero_3325_; 
v_zero_3324_ = lean_unsigned_to_nat(0u);
v_isZero_3325_ = lean_nat_dec_eq(v_x_3322_, v_zero_3324_);
if (v_isZero_3325_ == 1)
{
lean_dec(v_x_3322_);
lean_dec_ref(v_lctx_3319_);
return v_x_3323_;
}
else
{
lean_object* v_one_3326_; lean_object* v_n_3327_; lean_object* v_n_3329_; lean_object* v_ty_3330_; uint8_t v_bi_3331_; lean_object* v_x_3335_; lean_object* v___x_3336_; 
v_one_3326_ = lean_unsigned_to_nat(1u);
v_n_3327_ = lean_nat_sub(v_x_3322_, v_one_3326_);
lean_dec(v_x_3322_);
v_x_3335_ = lean_array_fget_borrowed(v_xs_3318_, v_n_3327_);
lean_inc_ref(v_lctx_3319_);
v___x_3336_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3319_, v_x_3335_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_dec_ref(v_x_3323_);
v___x_3337_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3338_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3337_);
v_x_3322_ = v_n_3327_;
v_x_3323_ = v___x_3338_;
goto _start;
}
else
{
lean_object* v_val_3340_; 
v_val_3340_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v___x_3336_, 1);
if (lean_obj_tag(v_val_3340_) == 0)
{
lean_object* v_userName_3341_; lean_object* v_type_3342_; uint8_t v_bi_3343_; 
v_userName_3341_ = lean_ctor_get(v_val_3340_, 2);
lean_inc(v_userName_3341_);
v_type_3342_ = lean_ctor_get(v_val_3340_, 3);
lean_inc_ref(v_type_3342_);
v_bi_3343_ = lean_ctor_get_uint8(v_val_3340_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3340_, 4);
v_n_3329_ = v_userName_3341_;
v_ty_3330_ = v_type_3342_;
v_bi_3331_ = v_bi_3343_;
goto v___jp_3328_;
}
else
{
lean_object* v_userName_3344_; lean_object* v_type_3345_; lean_object* v_value_3346_; uint8_t v_nondep_3347_; uint8_t v___y_3354_; 
v_userName_3344_ = lean_ctor_get(v_val_3340_, 2);
lean_inc(v_userName_3344_);
v_type_3345_ = lean_ctor_get(v_val_3340_, 3);
lean_inc_ref(v_type_3345_);
v_value_3346_ = lean_ctor_get(v_val_3340_, 4);
lean_inc_ref(v_value_3346_);
v_nondep_3347_ = lean_ctor_get_uint8(v_val_3340_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3340_, 5);
if (v_nondep_3347_ == 0)
{
v___y_3354_ = v_nondep_3347_;
goto v___jp_3353_;
}
else
{
if (v_generalizeNondepLet_3321_ == 0)
{
v___y_3354_ = v_generalizeNondepLet_3321_;
goto v___jp_3353_;
}
else
{
uint8_t v___x_3358_; 
lean_dec_ref(v_value_3346_);
v___x_3358_ = 0;
v_n_3329_ = v_userName_3344_;
v_ty_3330_ = v_type_3345_;
v_bi_3331_ = v___x_3358_;
goto v___jp_3328_;
}
}
v___jp_3348_:
{
lean_object* v_ty_3349_; lean_object* v_val_3350_; lean_object* v___x_3351_; 
v_ty_3349_ = lean_expr_abstract_range(v_type_3345_, v_n_3327_, v_xs_3318_);
lean_dec_ref(v_type_3345_);
v_val_3350_ = lean_expr_abstract_range(v_value_3346_, v_n_3327_, v_xs_3318_);
lean_dec_ref(v_value_3346_);
v___x_3351_ = l_Lean_Expr_letE___override(v_userName_3344_, v_ty_3349_, v_val_3350_, v_x_3323_, v_nondep_3347_);
v_x_3322_ = v_n_3327_;
v_x_3323_ = v___x_3351_;
goto _start;
}
v___jp_3353_:
{
if (v_usedLetOnly_3320_ == 0)
{
goto v___jp_3348_;
}
else
{
if (v___y_3354_ == 0)
{
uint8_t v___x_3355_; 
v___x_3355_ = lean_expr_has_loose_bvar(v_x_3323_, v_zero_3324_);
if (v___x_3355_ == 0)
{
lean_object* v___x_3356_; 
lean_dec_ref(v_value_3346_);
lean_dec_ref(v_type_3345_);
lean_dec(v_userName_3344_);
v___x_3356_ = lean_expr_lower_loose_bvars(v_x_3323_, v_one_3326_, v_one_3326_);
lean_dec_ref(v_x_3323_);
v_x_3322_ = v_n_3327_;
v_x_3323_ = v___x_3356_;
goto _start;
}
else
{
goto v___jp_3348_;
}
}
else
{
goto v___jp_3348_;
}
}
}
}
}
v___jp_3328_:
{
lean_object* v_ty_3332_; lean_object* v___x_3333_; 
v_ty_3332_ = lean_expr_abstract_range(v_ty_3330_, v_n_3327_, v_xs_3318_);
lean_dec_ref(v_ty_3330_);
v___x_3333_ = l_Lean_mkLambda(v_n_3329_, v_bi_3331_, v_ty_3332_, v_x_3323_);
v_x_3322_ = v_n_3327_;
v_x_3323_ = v___x_3333_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0___boxed(lean_object* v_xs_3359_, lean_object* v_lctx_3360_, lean_object* v_usedLetOnly_3361_, lean_object* v_generalizeNondepLet_3362_, lean_object* v_x_3363_, lean_object* v_x_3364_){
_start:
{
uint8_t v_usedLetOnly_boxed_3365_; uint8_t v_generalizeNondepLet_boxed_3366_; lean_object* v_res_3367_; 
v_usedLetOnly_boxed_3365_ = lean_unbox(v_usedLetOnly_3361_);
v_generalizeNondepLet_boxed_3366_ = lean_unbox(v_generalizeNondepLet_3362_);
v_res_3367_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3359_, v_lctx_3360_, v_usedLetOnly_boxed_3365_, v_generalizeNondepLet_boxed_3366_, v_x_3363_, v_x_3364_);
lean_dec_ref(v_xs_3359_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(lean_object* v_xs_3368_, lean_object* v_lctx_3369_, uint8_t v_usedLetOnly_3370_, uint8_t v_generalizeNondepLet_3371_, lean_object* v_x_3372_, lean_object* v_x_3373_){
_start:
{
lean_object* v_zero_3374_; uint8_t v_isZero_3375_; 
v_zero_3374_ = lean_unsigned_to_nat(0u);
v_isZero_3375_ = lean_nat_dec_eq(v_x_3372_, v_zero_3374_);
if (v_isZero_3375_ == 1)
{
lean_dec_ref(v_lctx_3369_);
return v_x_3373_;
}
else
{
lean_object* v_one_3376_; lean_object* v_n_3377_; lean_object* v_n_3379_; lean_object* v_ty_3380_; uint8_t v_bi_3381_; lean_object* v_x_3385_; lean_object* v___x_3386_; 
v_one_3376_ = lean_unsigned_to_nat(1u);
v_n_3377_ = lean_nat_sub(v_x_3372_, v_one_3376_);
v_x_3385_ = lean_array_fget_borrowed(v_xs_3368_, v_n_3377_);
lean_inc_ref(v_lctx_3369_);
v___x_3386_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3369_, v_x_3385_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_dec_ref(v_x_3373_);
v___x_3387_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3388_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3387_);
v___x_3389_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3368_, v_lctx_3369_, v_usedLetOnly_3370_, v_generalizeNondepLet_3371_, v_n_3377_, v___x_3388_);
return v___x_3389_;
}
else
{
lean_object* v_val_3390_; 
v_val_3390_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_val_3390_);
lean_dec_ref_known(v___x_3386_, 1);
if (lean_obj_tag(v_val_3390_) == 0)
{
lean_object* v_userName_3391_; lean_object* v_type_3392_; uint8_t v_bi_3393_; 
v_userName_3391_ = lean_ctor_get(v_val_3390_, 2);
lean_inc(v_userName_3391_);
v_type_3392_ = lean_ctor_get(v_val_3390_, 3);
lean_inc_ref(v_type_3392_);
v_bi_3393_ = lean_ctor_get_uint8(v_val_3390_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3390_, 4);
v_n_3379_ = v_userName_3391_;
v_ty_3380_ = v_type_3392_;
v_bi_3381_ = v_bi_3393_;
goto v___jp_3378_;
}
else
{
lean_object* v_userName_3394_; lean_object* v_type_3395_; lean_object* v_value_3396_; uint8_t v_nondep_3397_; uint8_t v___y_3404_; 
v_userName_3394_ = lean_ctor_get(v_val_3390_, 2);
lean_inc(v_userName_3394_);
v_type_3395_ = lean_ctor_get(v_val_3390_, 3);
lean_inc_ref(v_type_3395_);
v_value_3396_ = lean_ctor_get(v_val_3390_, 4);
lean_inc_ref(v_value_3396_);
v_nondep_3397_ = lean_ctor_get_uint8(v_val_3390_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3390_, 5);
if (v_nondep_3397_ == 0)
{
v___y_3404_ = v_nondep_3397_;
goto v___jp_3403_;
}
else
{
if (v_generalizeNondepLet_3371_ == 0)
{
v___y_3404_ = v_generalizeNondepLet_3371_;
goto v___jp_3403_;
}
else
{
uint8_t v___x_3408_; 
lean_dec_ref(v_value_3396_);
v___x_3408_ = 0;
v_n_3379_ = v_userName_3394_;
v_ty_3380_ = v_type_3395_;
v_bi_3381_ = v___x_3408_;
goto v___jp_3378_;
}
}
v___jp_3398_:
{
lean_object* v_ty_3399_; lean_object* v_val_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_ty_3399_ = lean_expr_abstract_range(v_type_3395_, v_n_3377_, v_xs_3368_);
lean_dec_ref(v_type_3395_);
v_val_3400_ = lean_expr_abstract_range(v_value_3396_, v_n_3377_, v_xs_3368_);
lean_dec_ref(v_value_3396_);
v___x_3401_ = l_Lean_Expr_letE___override(v_userName_3394_, v_ty_3399_, v_val_3400_, v_x_3373_, v_nondep_3397_);
v___x_3402_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3368_, v_lctx_3369_, v_usedLetOnly_3370_, v_generalizeNondepLet_3371_, v_n_3377_, v___x_3401_);
return v___x_3402_;
}
v___jp_3403_:
{
if (v_usedLetOnly_3370_ == 0)
{
goto v___jp_3398_;
}
else
{
if (v___y_3404_ == 0)
{
uint8_t v___x_3405_; 
v___x_3405_ = lean_expr_has_loose_bvar(v_x_3373_, v_zero_3374_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
lean_dec_ref(v_value_3396_);
lean_dec_ref(v_type_3395_);
lean_dec(v_userName_3394_);
v___x_3406_ = lean_expr_lower_loose_bvars(v_x_3373_, v_one_3376_, v_one_3376_);
lean_dec_ref(v_x_3373_);
v___x_3407_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3368_, v_lctx_3369_, v_usedLetOnly_3370_, v_generalizeNondepLet_3371_, v_n_3377_, v___x_3406_);
return v___x_3407_;
}
else
{
goto v___jp_3398_;
}
}
else
{
goto v___jp_3398_;
}
}
}
}
}
v___jp_3378_:
{
lean_object* v_ty_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v_ty_3382_ = lean_expr_abstract_range(v_ty_3380_, v_n_3377_, v_xs_3368_);
lean_dec_ref(v_ty_3380_);
v___x_3383_ = l_Lean_mkLambda(v_n_3379_, v_bi_3381_, v_ty_3382_, v_x_3373_);
v___x_3384_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0_spec__0(v_xs_3368_, v_lctx_3369_, v_usedLetOnly_3370_, v_generalizeNondepLet_3371_, v_n_3377_, v___x_3383_);
return v___x_3384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0___boxed(lean_object* v_xs_3409_, lean_object* v_lctx_3410_, lean_object* v_usedLetOnly_3411_, lean_object* v_generalizeNondepLet_3412_, lean_object* v_x_3413_, lean_object* v_x_3414_){
_start:
{
uint8_t v_usedLetOnly_boxed_3415_; uint8_t v_generalizeNondepLet_boxed_3416_; lean_object* v_res_3417_; 
v_usedLetOnly_boxed_3415_ = lean_unbox(v_usedLetOnly_3411_);
v_generalizeNondepLet_boxed_3416_ = lean_unbox(v_generalizeNondepLet_3412_);
v_res_3417_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3409_, v_lctx_3410_, v_usedLetOnly_boxed_3415_, v_generalizeNondepLet_boxed_3416_, v_x_3413_, v_x_3414_);
lean_dec(v_x_3413_);
lean_dec_ref(v_xs_3409_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda(lean_object* v_lctx_3418_, lean_object* v_xs_3419_, lean_object* v_b_3420_, uint8_t v_usedLetOnly_3421_, uint8_t v_generalizeNondepLet_3422_){
_start:
{
lean_object* v_b_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v_b_3423_ = lean_expr_abstract(v_b_3420_, v_xs_3419_);
v___x_3424_ = lean_array_get_size(v_xs_3419_);
v___x_3425_ = l_Nat_foldRev___at___00Lean_LocalContext_mkLambda_spec__0(v_xs_3419_, v_lctx_3418_, v_usedLetOnly_3421_, v_generalizeNondepLet_3422_, v___x_3424_, v_b_3423_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkLambda___boxed(lean_object* v_lctx_3426_, lean_object* v_xs_3427_, lean_object* v_b_3428_, lean_object* v_usedLetOnly_3429_, lean_object* v_generalizeNondepLet_3430_){
_start:
{
uint8_t v_usedLetOnly_boxed_3431_; uint8_t v_generalizeNondepLet_boxed_3432_; lean_object* v_res_3433_; 
v_usedLetOnly_boxed_3431_ = lean_unbox(v_usedLetOnly_3429_);
v_generalizeNondepLet_boxed_3432_ = lean_unbox(v_generalizeNondepLet_3430_);
v_res_3433_ = l_Lean_LocalContext_mkLambda(v_lctx_3426_, v_xs_3427_, v_b_3428_, v_usedLetOnly_boxed_3431_, v_generalizeNondepLet_boxed_3432_);
lean_dec_ref(v_b_3428_);
lean_dec_ref(v_xs_3427_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(lean_object* v_xs_3434_, lean_object* v_lctx_3435_, uint8_t v_usedLetOnly_3436_, uint8_t v_generalizeNondepLet_3437_, lean_object* v_x_3438_, lean_object* v_x_3439_){
_start:
{
lean_object* v_zero_3440_; uint8_t v_isZero_3441_; 
v_zero_3440_ = lean_unsigned_to_nat(0u);
v_isZero_3441_ = lean_nat_dec_eq(v_x_3438_, v_zero_3440_);
if (v_isZero_3441_ == 1)
{
lean_dec(v_x_3438_);
lean_dec_ref(v_lctx_3435_);
return v_x_3439_;
}
else
{
lean_object* v_one_3442_; lean_object* v_n_3443_; lean_object* v_n_3445_; lean_object* v_ty_3446_; uint8_t v_bi_3447_; lean_object* v_x_3451_; lean_object* v___x_3452_; 
v_one_3442_ = lean_unsigned_to_nat(1u);
v_n_3443_ = lean_nat_sub(v_x_3438_, v_one_3442_);
lean_dec(v_x_3438_);
v_x_3451_ = lean_array_fget_borrowed(v_xs_3434_, v_n_3443_);
lean_inc_ref(v_lctx_3435_);
v___x_3452_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3435_, v_x_3451_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
lean_dec_ref(v_x_3439_);
v___x_3453_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3454_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3453_);
v_x_3438_ = v_n_3443_;
v_x_3439_ = v___x_3454_;
goto _start;
}
else
{
lean_object* v_val_3456_; 
v_val_3456_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_val_3456_);
lean_dec_ref_known(v___x_3452_, 1);
if (lean_obj_tag(v_val_3456_) == 0)
{
lean_object* v_userName_3457_; lean_object* v_type_3458_; uint8_t v_bi_3459_; 
v_userName_3457_ = lean_ctor_get(v_val_3456_, 2);
lean_inc(v_userName_3457_);
v_type_3458_ = lean_ctor_get(v_val_3456_, 3);
lean_inc_ref(v_type_3458_);
v_bi_3459_ = lean_ctor_get_uint8(v_val_3456_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3456_, 4);
v_n_3445_ = v_userName_3457_;
v_ty_3446_ = v_type_3458_;
v_bi_3447_ = v_bi_3459_;
goto v___jp_3444_;
}
else
{
lean_object* v_userName_3460_; lean_object* v_type_3461_; lean_object* v_value_3462_; uint8_t v_nondep_3463_; uint8_t v___y_3470_; 
v_userName_3460_ = lean_ctor_get(v_val_3456_, 2);
lean_inc(v_userName_3460_);
v_type_3461_ = lean_ctor_get(v_val_3456_, 3);
lean_inc_ref(v_type_3461_);
v_value_3462_ = lean_ctor_get(v_val_3456_, 4);
lean_inc_ref(v_value_3462_);
v_nondep_3463_ = lean_ctor_get_uint8(v_val_3456_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3456_, 5);
if (v_nondep_3463_ == 0)
{
v___y_3470_ = v_nondep_3463_;
goto v___jp_3469_;
}
else
{
if (v_generalizeNondepLet_3437_ == 0)
{
v___y_3470_ = v_generalizeNondepLet_3437_;
goto v___jp_3469_;
}
else
{
uint8_t v___x_3474_; 
lean_dec_ref(v_value_3462_);
v___x_3474_ = 0;
v_n_3445_ = v_userName_3460_;
v_ty_3446_ = v_type_3461_;
v_bi_3447_ = v___x_3474_;
goto v___jp_3444_;
}
}
v___jp_3464_:
{
lean_object* v_ty_3465_; lean_object* v_val_3466_; lean_object* v___x_3467_; 
v_ty_3465_ = lean_expr_abstract_range(v_type_3461_, v_n_3443_, v_xs_3434_);
lean_dec_ref(v_type_3461_);
v_val_3466_ = lean_expr_abstract_range(v_value_3462_, v_n_3443_, v_xs_3434_);
lean_dec_ref(v_value_3462_);
v___x_3467_ = l_Lean_Expr_letE___override(v_userName_3460_, v_ty_3465_, v_val_3466_, v_x_3439_, v_nondep_3463_);
v_x_3438_ = v_n_3443_;
v_x_3439_ = v___x_3467_;
goto _start;
}
v___jp_3469_:
{
if (v_usedLetOnly_3436_ == 0)
{
goto v___jp_3464_;
}
else
{
if (v___y_3470_ == 0)
{
uint8_t v___x_3471_; 
v___x_3471_ = lean_expr_has_loose_bvar(v_x_3439_, v_zero_3440_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; 
lean_dec_ref(v_value_3462_);
lean_dec_ref(v_type_3461_);
lean_dec(v_userName_3460_);
v___x_3472_ = lean_expr_lower_loose_bvars(v_x_3439_, v_one_3442_, v_one_3442_);
lean_dec_ref(v_x_3439_);
v_x_3438_ = v_n_3443_;
v_x_3439_ = v___x_3472_;
goto _start;
}
else
{
goto v___jp_3464_;
}
}
else
{
goto v___jp_3464_;
}
}
}
}
}
v___jp_3444_:
{
lean_object* v_ty_3448_; lean_object* v___x_3449_; 
v_ty_3448_ = lean_expr_abstract_range(v_ty_3446_, v_n_3443_, v_xs_3434_);
lean_dec_ref(v_ty_3446_);
v___x_3449_ = l_Lean_mkForall(v_n_3445_, v_bi_3447_, v_ty_3448_, v_x_3439_);
v_x_3438_ = v_n_3443_;
v_x_3439_ = v___x_3449_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0___boxed(lean_object* v_xs_3475_, lean_object* v_lctx_3476_, lean_object* v_usedLetOnly_3477_, lean_object* v_generalizeNondepLet_3478_, lean_object* v_x_3479_, lean_object* v_x_3480_){
_start:
{
uint8_t v_usedLetOnly_boxed_3481_; uint8_t v_generalizeNondepLet_boxed_3482_; lean_object* v_res_3483_; 
v_usedLetOnly_boxed_3481_ = lean_unbox(v_usedLetOnly_3477_);
v_generalizeNondepLet_boxed_3482_ = lean_unbox(v_generalizeNondepLet_3478_);
v_res_3483_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3475_, v_lctx_3476_, v_usedLetOnly_boxed_3481_, v_generalizeNondepLet_boxed_3482_, v_x_3479_, v_x_3480_);
lean_dec_ref(v_xs_3475_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(lean_object* v_xs_3484_, lean_object* v_lctx_3485_, uint8_t v_usedLetOnly_3486_, uint8_t v_generalizeNondepLet_3487_, lean_object* v_x_3488_, lean_object* v_x_3489_){
_start:
{
lean_object* v_zero_3490_; uint8_t v_isZero_3491_; 
v_zero_3490_ = lean_unsigned_to_nat(0u);
v_isZero_3491_ = lean_nat_dec_eq(v_x_3488_, v_zero_3490_);
if (v_isZero_3491_ == 1)
{
lean_dec_ref(v_lctx_3485_);
return v_x_3489_;
}
else
{
lean_object* v_one_3492_; lean_object* v_n_3493_; lean_object* v_n_3495_; lean_object* v_ty_3496_; uint8_t v_bi_3497_; lean_object* v_x_3501_; lean_object* v___x_3502_; 
v_one_3492_ = lean_unsigned_to_nat(1u);
v_n_3493_ = lean_nat_sub(v_x_3488_, v_one_3492_);
v_x_3501_ = lean_array_fget_borrowed(v_xs_3484_, v_n_3493_);
lean_inc_ref(v_lctx_3485_);
v___x_3502_ = l_Lean_LocalContext_findFVar_x3f(v_lctx_3485_, v_x_3501_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
lean_dec_ref(v_x_3489_);
v___x_3503_ = lean_obj_once(&l_Lean_LocalContext_mkBinding___lam__0___closed__1, &l_Lean_LocalContext_mkBinding___lam__0___closed__1_once, _init_l_Lean_LocalContext_mkBinding___lam__0___closed__1);
v___x_3504_ = l_panic___at___00Lean_LocalDecl_value_spec__0(v___x_3503_);
v___x_3505_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3484_, v_lctx_3485_, v_usedLetOnly_3486_, v_generalizeNondepLet_3487_, v_n_3493_, v___x_3504_);
return v___x_3505_;
}
else
{
lean_object* v_val_3506_; 
v_val_3506_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_val_3506_);
lean_dec_ref_known(v___x_3502_, 1);
if (lean_obj_tag(v_val_3506_) == 0)
{
lean_object* v_userName_3507_; lean_object* v_type_3508_; uint8_t v_bi_3509_; 
v_userName_3507_ = lean_ctor_get(v_val_3506_, 2);
lean_inc(v_userName_3507_);
v_type_3508_ = lean_ctor_get(v_val_3506_, 3);
lean_inc_ref(v_type_3508_);
v_bi_3509_ = lean_ctor_get_uint8(v_val_3506_, sizeof(void*)*4);
lean_dec_ref_known(v_val_3506_, 4);
v_n_3495_ = v_userName_3507_;
v_ty_3496_ = v_type_3508_;
v_bi_3497_ = v_bi_3509_;
goto v___jp_3494_;
}
else
{
lean_object* v_userName_3510_; lean_object* v_type_3511_; lean_object* v_value_3512_; uint8_t v_nondep_3513_; uint8_t v___y_3520_; 
v_userName_3510_ = lean_ctor_get(v_val_3506_, 2);
lean_inc(v_userName_3510_);
v_type_3511_ = lean_ctor_get(v_val_3506_, 3);
lean_inc_ref(v_type_3511_);
v_value_3512_ = lean_ctor_get(v_val_3506_, 4);
lean_inc_ref(v_value_3512_);
v_nondep_3513_ = lean_ctor_get_uint8(v_val_3506_, sizeof(void*)*5);
lean_dec_ref_known(v_val_3506_, 5);
if (v_nondep_3513_ == 0)
{
v___y_3520_ = v_nondep_3513_;
goto v___jp_3519_;
}
else
{
if (v_generalizeNondepLet_3487_ == 0)
{
v___y_3520_ = v_generalizeNondepLet_3487_;
goto v___jp_3519_;
}
else
{
uint8_t v___x_3524_; 
lean_dec_ref(v_value_3512_);
v___x_3524_ = 0;
v_n_3495_ = v_userName_3510_;
v_ty_3496_ = v_type_3511_;
v_bi_3497_ = v___x_3524_;
goto v___jp_3494_;
}
}
v___jp_3514_:
{
lean_object* v_ty_3515_; lean_object* v_val_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v_ty_3515_ = lean_expr_abstract_range(v_type_3511_, v_n_3493_, v_xs_3484_);
lean_dec_ref(v_type_3511_);
v_val_3516_ = lean_expr_abstract_range(v_value_3512_, v_n_3493_, v_xs_3484_);
lean_dec_ref(v_value_3512_);
v___x_3517_ = l_Lean_Expr_letE___override(v_userName_3510_, v_ty_3515_, v_val_3516_, v_x_3489_, v_nondep_3513_);
v___x_3518_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3484_, v_lctx_3485_, v_usedLetOnly_3486_, v_generalizeNondepLet_3487_, v_n_3493_, v___x_3517_);
return v___x_3518_;
}
v___jp_3519_:
{
if (v_usedLetOnly_3486_ == 0)
{
goto v___jp_3514_;
}
else
{
if (v___y_3520_ == 0)
{
uint8_t v___x_3521_; 
v___x_3521_ = lean_expr_has_loose_bvar(v_x_3489_, v_zero_3490_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_dec_ref(v_value_3512_);
lean_dec_ref(v_type_3511_);
lean_dec(v_userName_3510_);
v___x_3522_ = lean_expr_lower_loose_bvars(v_x_3489_, v_one_3492_, v_one_3492_);
lean_dec_ref(v_x_3489_);
v___x_3523_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3484_, v_lctx_3485_, v_usedLetOnly_3486_, v_generalizeNondepLet_3487_, v_n_3493_, v___x_3522_);
return v___x_3523_;
}
else
{
goto v___jp_3514_;
}
}
else
{
goto v___jp_3514_;
}
}
}
}
}
v___jp_3494_:
{
lean_object* v_ty_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v_ty_3498_ = lean_expr_abstract_range(v_ty_3496_, v_n_3493_, v_xs_3484_);
lean_dec_ref(v_ty_3496_);
v___x_3499_ = l_Lean_mkForall(v_n_3495_, v_bi_3497_, v_ty_3498_, v_x_3489_);
v___x_3500_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0_spec__0(v_xs_3484_, v_lctx_3485_, v_usedLetOnly_3486_, v_generalizeNondepLet_3487_, v_n_3493_, v___x_3499_);
return v___x_3500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0___boxed(lean_object* v_xs_3525_, lean_object* v_lctx_3526_, lean_object* v_usedLetOnly_3527_, lean_object* v_generalizeNondepLet_3528_, lean_object* v_x_3529_, lean_object* v_x_3530_){
_start:
{
uint8_t v_usedLetOnly_boxed_3531_; uint8_t v_generalizeNondepLet_boxed_3532_; lean_object* v_res_3533_; 
v_usedLetOnly_boxed_3531_ = lean_unbox(v_usedLetOnly_3527_);
v_generalizeNondepLet_boxed_3532_ = lean_unbox(v_generalizeNondepLet_3528_);
v_res_3533_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3525_, v_lctx_3526_, v_usedLetOnly_boxed_3531_, v_generalizeNondepLet_boxed_3532_, v_x_3529_, v_x_3530_);
lean_dec(v_x_3529_);
lean_dec_ref(v_xs_3525_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall(lean_object* v_lctx_3534_, lean_object* v_xs_3535_, lean_object* v_b_3536_, uint8_t v_usedLetOnly_3537_, uint8_t v_generalizeNondepLet_3538_){
_start:
{
lean_object* v_b_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v_b_3539_ = lean_expr_abstract(v_b_3536_, v_xs_3535_);
v___x_3540_ = lean_array_get_size(v_xs_3535_);
v___x_3541_ = l_Nat_foldRev___at___00Lean_LocalContext_mkForall_spec__0(v_xs_3535_, v_lctx_3534_, v_usedLetOnly_3537_, v_generalizeNondepLet_3538_, v___x_3540_, v_b_3539_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_mkForall___boxed(lean_object* v_lctx_3542_, lean_object* v_xs_3543_, lean_object* v_b_3544_, lean_object* v_usedLetOnly_3545_, lean_object* v_generalizeNondepLet_3546_){
_start:
{
uint8_t v_usedLetOnly_boxed_3547_; uint8_t v_generalizeNondepLet_boxed_3548_; lean_object* v_res_3549_; 
v_usedLetOnly_boxed_3547_ = lean_unbox(v_usedLetOnly_3545_);
v_generalizeNondepLet_boxed_3548_ = lean_unbox(v_generalizeNondepLet_3546_);
v_res_3549_ = l_Lean_LocalContext_mkForall(v_lctx_3542_, v_xs_3543_, v_b_3544_, v_usedLetOnly_boxed_3547_, v_generalizeNondepLet_boxed_3548_);
lean_dec_ref(v_b_3544_);
lean_dec_ref(v_xs_3543_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg___lam__0(lean_object* v_toPure_3550_, lean_object* v_p_3551_, lean_object* v_d_3552_){
_start:
{
if (lean_obj_tag(v_d_3552_) == 0)
{
uint8_t v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
lean_dec(v_p_3551_);
v___x_3553_ = 0;
v___x_3554_ = lean_box(v___x_3553_);
v___x_3555_ = lean_apply_2(v_toPure_3550_, lean_box(0), v___x_3554_);
return v___x_3555_;
}
else
{
lean_object* v_val_3556_; lean_object* v___x_3557_; 
lean_dec(v_toPure_3550_);
v_val_3556_ = lean_ctor_get(v_d_3552_, 0);
lean_inc(v_val_3556_);
lean_dec_ref_known(v_d_3552_, 1);
v___x_3557_ = lean_apply_1(v_p_3551_, v_val_3556_);
return v___x_3557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM___redArg(lean_object* v_inst_3558_, lean_object* v_lctx_3559_, lean_object* v_p_3560_){
_start:
{
lean_object* v_toApplicative_3561_; lean_object* v_decls_3562_; lean_object* v_toPure_3563_; lean_object* v___f_3564_; lean_object* v___x_3565_; 
v_toApplicative_3561_ = lean_ctor_get(v_inst_3558_, 0);
v_decls_3562_ = lean_ctor_get(v_lctx_3559_, 1);
lean_inc_ref(v_decls_3562_);
lean_dec_ref(v_lctx_3559_);
v_toPure_3563_ = lean_ctor_get(v_toApplicative_3561_, 1);
lean_inc(v_toPure_3563_);
v___f_3564_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3564_, 0, v_toPure_3563_);
lean_closure_set(v___f_3564_, 1, v_p_3560_);
v___x_3565_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3558_, v_decls_3562_, v___f_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_anyM(lean_object* v_m_3566_, lean_object* v_inst_3567_, lean_object* v_lctx_3568_, lean_object* v_p_3569_){
_start:
{
lean_object* v_toApplicative_3570_; lean_object* v_decls_3571_; lean_object* v_toPure_3572_; lean_object* v___f_3573_; lean_object* v___x_3574_; 
v_toApplicative_3570_ = lean_ctor_get(v_inst_3567_, 0);
v_decls_3571_ = lean_ctor_get(v_lctx_3568_, 1);
lean_inc_ref(v_decls_3571_);
lean_dec_ref(v_lctx_3568_);
v_toPure_3572_ = lean_ctor_get(v_toApplicative_3570_, 1);
lean_inc(v_toPure_3572_);
v___f_3573_ = lean_alloc_closure((void*)(l_Lean_LocalContext_anyM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3573_, 0, v_toPure_3572_);
lean_closure_set(v___f_3573_, 1, v_p_3569_);
v___x_3574_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3567_, v_decls_3571_, v___f_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0(lean_object* v_toPure_3575_, uint8_t v_b_3576_){
_start:
{
if (v_b_3576_ == 0)
{
uint8_t v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3577_ = 1;
v___x_3578_ = lean_box(v___x_3577_);
v___x_3579_ = lean_apply_2(v_toPure_3575_, lean_box(0), v___x_3578_);
return v___x_3579_;
}
else
{
uint8_t v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3580_ = 0;
v___x_3581_ = lean_box(v___x_3580_);
v___x_3582_ = lean_apply_2(v_toPure_3575_, lean_box(0), v___x_3581_);
return v___x_3582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__0___boxed(lean_object* v_toPure_3583_, lean_object* v_b_3584_){
_start:
{
uint8_t v_b_boxed_3585_; lean_object* v_res_3586_; 
v_b_boxed_3585_ = lean_unbox(v_b_3584_);
v_res_3586_ = l_Lean_LocalContext_allM___redArg___lam__0(v_toPure_3583_, v_b_boxed_3585_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg___lam__2(lean_object* v_toPure_3587_, lean_object* v_toBind_3588_, lean_object* v___f_3589_, lean_object* v_p_3590_, lean_object* v_v_3591_){
_start:
{
if (lean_obj_tag(v_v_3591_) == 0)
{
uint8_t v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
lean_dec(v_p_3590_);
v___x_3592_ = 1;
v___x_3593_ = lean_box(v___x_3592_);
v___x_3594_ = lean_apply_2(v_toPure_3587_, lean_box(0), v___x_3593_);
v___x_3595_ = lean_apply_4(v_toBind_3588_, lean_box(0), lean_box(0), v___x_3594_, v___f_3589_);
return v___x_3595_;
}
else
{
lean_object* v_val_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
lean_dec(v_toPure_3587_);
v_val_3596_ = lean_ctor_get(v_v_3591_, 0);
lean_inc(v_val_3596_);
lean_dec_ref_known(v_v_3591_, 1);
v___x_3597_ = lean_apply_1(v_p_3590_, v_val_3596_);
v___x_3598_ = lean_apply_4(v_toBind_3588_, lean_box(0), lean_box(0), v___x_3597_, v___f_3589_);
return v___x_3598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM___redArg(lean_object* v_inst_3599_, lean_object* v_lctx_3600_, lean_object* v_p_3601_){
_start:
{
lean_object* v_toApplicative_3602_; lean_object* v_decls_3603_; lean_object* v_toBind_3604_; lean_object* v_toPure_3605_; lean_object* v___f_3606_; lean_object* v___f_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v_toApplicative_3602_ = lean_ctor_get(v_inst_3599_, 0);
v_decls_3603_ = lean_ctor_get(v_lctx_3600_, 1);
lean_inc_ref(v_decls_3603_);
lean_dec_ref(v_lctx_3600_);
v_toBind_3604_ = lean_ctor_get(v_inst_3599_, 1);
lean_inc_n(v_toBind_3604_, 2);
v_toPure_3605_ = lean_ctor_get(v_toApplicative_3602_, 1);
lean_inc_n(v_toPure_3605_, 2);
v___f_3606_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3606_, 0, v_toPure_3605_);
lean_inc_ref(v___f_3606_);
v___f_3607_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3607_, 0, v_toPure_3605_);
lean_closure_set(v___f_3607_, 1, v_toBind_3604_);
lean_closure_set(v___f_3607_, 2, v___f_3606_);
lean_closure_set(v___f_3607_, 3, v_p_3601_);
v___x_3608_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3599_, v_decls_3603_, v___f_3607_);
v___x_3609_ = lean_apply_4(v_toBind_3604_, lean_box(0), lean_box(0), v___x_3608_, v___f_3606_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_allM(lean_object* v_m_3610_, lean_object* v_inst_3611_, lean_object* v_lctx_3612_, lean_object* v_p_3613_){
_start:
{
lean_object* v_toApplicative_3614_; lean_object* v_decls_3615_; lean_object* v_toBind_3616_; lean_object* v_toPure_3617_; lean_object* v___f_3618_; lean_object* v___f_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v_toApplicative_3614_ = lean_ctor_get(v_inst_3611_, 0);
v_decls_3615_ = lean_ctor_get(v_lctx_3612_, 1);
lean_inc_ref(v_decls_3615_);
lean_dec_ref(v_lctx_3612_);
v_toBind_3616_ = lean_ctor_get(v_inst_3611_, 1);
lean_inc_n(v_toBind_3616_, 2);
v_toPure_3617_ = lean_ctor_get(v_toApplicative_3614_, 1);
lean_inc_n(v_toPure_3617_, 2);
v___f_3618_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3618_, 0, v_toPure_3617_);
lean_inc_ref(v___f_3618_);
v___f_3619_ = lean_alloc_closure((void*)(l_Lean_LocalContext_allM___redArg___lam__2), 5, 4);
lean_closure_set(v___f_3619_, 0, v_toPure_3617_);
lean_closure_set(v___f_3619_, 1, v_toBind_3616_);
lean_closure_set(v___f_3619_, 2, v___f_3618_);
lean_closure_set(v___f_3619_, 3, v_p_3613_);
v___x_3620_ = l_Lean_PersistentArray_anyM___redArg(v_inst_3611_, v_decls_3615_, v___f_3619_);
v___x_3621_ = lean_apply_4(v_toBind_3616_, lean_box(0), lean_box(0), v___x_3620_, v___f_3618_);
return v___x_3621_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any___lam__0(lean_object* v_p_3622_, lean_object* v_d_3623_){
_start:
{
if (lean_obj_tag(v_d_3623_) == 0)
{
uint8_t v___x_3624_; 
lean_dec_ref(v_p_3622_);
v___x_3624_ = 0;
return v___x_3624_;
}
else
{
lean_object* v_val_3625_; lean_object* v___x_3626_; uint8_t v___x_3627_; 
v_val_3625_ = lean_ctor_get(v_d_3623_, 0);
lean_inc(v_val_3625_);
lean_dec_ref_known(v_d_3623_, 1);
v___x_3626_ = lean_apply_1(v_p_3622_, v_val_3625_);
v___x_3627_ = lean_unbox(v___x_3626_);
return v___x_3627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___lam__0___boxed(lean_object* v_p_3628_, lean_object* v_d_3629_){
_start:
{
uint8_t v_res_3630_; lean_object* v_r_3631_; 
v_res_3630_ = l_Lean_LocalContext_any___lam__0(v_p_3628_, v_d_3629_);
v_r_3631_ = lean_box(v_res_3630_);
return v_r_3631_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_any(lean_object* v_lctx_3632_, lean_object* v_p_3633_){
_start:
{
lean_object* v___x_3634_; lean_object* v_decls_3635_; lean_object* v___f_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3634_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3635_ = lean_ctor_get(v_lctx_3632_, 1);
lean_inc_ref(v_decls_3635_);
lean_dec_ref(v_lctx_3632_);
v___f_3636_ = lean_alloc_closure((void*)(l_Lean_LocalContext_any___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3636_, 0, v_p_3633_);
v___x_3637_ = l_Lean_PersistentArray_anyM___redArg(v___x_3634_, v_decls_3635_, v___f_3636_);
v___x_3638_ = lean_unbox(v___x_3637_);
lean_dec(v___x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_any___boxed(lean_object* v_lctx_3639_, lean_object* v_p_3640_){
_start:
{
uint8_t v_res_3641_; lean_object* v_r_3642_; 
v_res_3641_ = l_Lean_LocalContext_any(v_lctx_3639_, v_p_3640_);
v_r_3642_ = lean_box(v_res_3641_);
return v_r_3642_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all___lam__0(lean_object* v_p_3643_, lean_object* v_v_3644_){
_start:
{
if (lean_obj_tag(v_v_3644_) == 0)
{
uint8_t v___x_3645_; 
lean_dec_ref(v_p_3643_);
v___x_3645_ = 0;
return v___x_3645_;
}
else
{
lean_object* v_val_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v_val_3646_ = lean_ctor_get(v_v_3644_, 0);
lean_inc(v_val_3646_);
lean_dec_ref_known(v_v_3644_, 1);
v___x_3647_ = lean_apply_1(v_p_3643_, v_val_3646_);
v___x_3648_ = lean_unbox(v___x_3647_);
if (v___x_3648_ == 0)
{
uint8_t v___x_3649_; 
v___x_3649_ = 1;
return v___x_3649_;
}
else
{
uint8_t v___x_3650_; 
v___x_3650_ = 0;
return v___x_3650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___lam__0___boxed(lean_object* v_p_3651_, lean_object* v_v_3652_){
_start:
{
uint8_t v_res_3653_; lean_object* v_r_3654_; 
v_res_3653_ = l_Lean_LocalContext_all___lam__0(v_p_3651_, v_v_3652_);
v_r_3654_ = lean_box(v_res_3653_);
return v_r_3654_;
}
}
LEAN_EXPORT uint8_t l_Lean_LocalContext_all(lean_object* v_lctx_3655_, lean_object* v_p_3656_){
_start:
{
lean_object* v___x_3657_; lean_object* v_decls_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v___x_3657_ = ((lean_object*)(l_Lean_LocalContext_foldl___redArg___closed__9));
v_decls_3658_ = lean_ctor_get(v_lctx_3655_, 1);
lean_inc_ref(v_decls_3658_);
lean_dec_ref(v_lctx_3655_);
v___f_3659_ = lean_alloc_closure((void*)(l_Lean_LocalContext_all___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3659_, 0, v_p_3656_);
v___x_3660_ = l_Lean_PersistentArray_anyM___redArg(v___x_3657_, v_decls_3658_, v___f_3659_);
v___x_3661_ = lean_unbox(v___x_3660_);
lean_dec(v___x_3660_);
if (v___x_3661_ == 0)
{
uint8_t v___x_3662_; 
v___x_3662_ = 1;
return v___x_3662_;
}
else
{
uint8_t v___x_3663_; 
v___x_3663_ = 0;
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_all___boxed(lean_object* v_lctx_3664_, lean_object* v_p_3665_){
_start:
{
uint8_t v_res_3666_; lean_object* v_r_3667_; 
v_res_3666_ = l_Lean_LocalContext_all(v_lctx_3664_, v_p_3665_);
v_r_3667_ = lean_box(v_res_3666_);
return v_r_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(lean_object* v_i_3668_, lean_object* v_a_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_zero_3672_; uint8_t v_isZero_3673_; 
v_zero_3672_ = lean_unsigned_to_nat(0u);
v_isZero_3673_ = lean_nat_dec_eq(v_i_3668_, v_zero_3672_);
if (v_isZero_3673_ == 1)
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
lean_dec(v_i_3668_);
v___x_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3674_, 0, v_a_3669_);
lean_ctor_set(v___x_3674_, 1, v___y_3670_);
v___x_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
lean_ctor_set(v___x_3675_, 1, v___y_3671_);
return v___x_3675_;
}
else
{
lean_object* v_decls_3676_; lean_object* v_size_3677_; lean_object* v___x_3678_; lean_object* v_one_3679_; lean_object* v_n_3680_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3697_; lean_object* v___y_3698_; uint8_t v___y_3699_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3709_; uint8_t v___x_3713_; 
v_decls_3676_ = lean_ctor_get(v_a_3669_, 1);
v_size_3677_ = lean_ctor_get(v_decls_3676_, 2);
v___x_3678_ = lean_box(0);
v_one_3679_ = lean_unsigned_to_nat(1u);
v_n_3680_ = lean_nat_sub(v_i_3668_, v_one_3679_);
lean_dec(v_i_3668_);
v___x_3713_ = lean_nat_dec_lt(v_n_3680_, v_size_3677_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; 
v___x_3714_ = l_outOfBounds___redArg(v___x_3678_);
v___y_3709_ = v___x_3714_;
goto v___jp_3708_;
}
else
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3678_, v_decls_3676_, v_n_3680_);
v___y_3709_ = v___x_3715_;
goto v___jp_3708_;
}
v___jp_3681_:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_LocalContext_setUserName(v_a_3669_, v___y_3685_, v___y_3683_);
v_i_3668_ = v_n_3680_;
v_a_3669_ = v___x_3686_;
v___y_3670_ = v___y_3682_;
v___y_3671_ = v___y_3684_;
goto _start;
}
v___jp_3688_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v_fst_3693_; lean_object* v_snd_3694_; lean_object* v_fvarId_3695_; 
lean_inc(v___y_3690_);
v___x_3691_ = l_Lean_NameSet_insert(v___y_3670_, v___y_3690_);
v___x_3692_ = l_Lean_sanitizeName(v___y_3690_, v___y_3671_);
v_fst_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_fst_3693_);
v_snd_3694_ = lean_ctor_get(v___x_3692_, 1);
lean_inc(v_snd_3694_);
lean_dec_ref(v___x_3692_);
v_fvarId_3695_ = lean_ctor_get(v___y_3689_, 1);
lean_inc(v_fvarId_3695_);
lean_dec_ref(v___y_3689_);
v___y_3682_ = v___x_3691_;
v___y_3683_ = v_fst_3693_;
v___y_3684_ = v_snd_3694_;
v___y_3685_ = v_fvarId_3695_;
goto v___jp_3681_;
}
v___jp_3696_:
{
if (v___y_3699_ == 0)
{
lean_object* v___x_3700_; 
lean_dec_ref(v___y_3697_);
v___x_3700_ = l_Lean_NameSet_insert(v___y_3670_, v___y_3698_);
v_i_3668_ = v_n_3680_;
v___y_3670_ = v___x_3700_;
goto _start;
}
else
{
v___y_3689_ = v___y_3697_;
v___y_3690_ = v___y_3698_;
goto v___jp_3688_;
}
}
v___jp_3702_:
{
uint8_t v___x_3705_; 
v___x_3705_ = l_Lean_Name_hasMacroScopes(v___y_3704_);
if (v___x_3705_ == 0)
{
lean_object* v_userName_3706_; uint8_t v___x_3707_; 
v_userName_3706_ = lean_ctor_get(v___y_3703_, 2);
v___x_3707_ = l_Lean_NameSet_contains(v___y_3670_, v_userName_3706_);
v___y_3697_ = v___y_3703_;
v___y_3698_ = v___y_3704_;
v___y_3699_ = v___x_3707_;
goto v___jp_3696_;
}
else
{
v___y_3689_ = v___y_3703_;
v___y_3690_ = v___y_3704_;
goto v___jp_3688_;
}
}
v___jp_3708_:
{
if (lean_obj_tag(v___y_3709_) == 0)
{
v_i_3668_ = v_n_3680_;
goto _start;
}
else
{
lean_object* v_val_3711_; lean_object* v_userName_3712_; 
v_val_3711_ = lean_ctor_get(v___y_3709_, 0);
lean_inc(v_val_3711_);
lean_dec_ref_known(v___y_3709_, 1);
v_userName_3712_ = lean_ctor_get(v_val_3711_, 2);
lean_inc(v_userName_3712_);
v___y_3703_ = v_val_3711_;
v___y_3704_ = v_userName_3712_;
goto v___jp_3702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sanitizeNames(lean_object* v_lctx_3716_, lean_object* v_a_3717_){
_start:
{
lean_object* v_options_3718_; uint8_t v___x_3719_; 
v_options_3718_ = lean_ctor_get(v_a_3717_, 0);
v___x_3719_ = l_Lean_getSanitizeNames(v_options_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3720_, 0, v_lctx_3716_);
lean_ctor_set(v___x_3720_, 1, v_a_3717_);
return v___x_3720_;
}
else
{
lean_object* v_decls_3721_; lean_object* v_size_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v_fst_3725_; lean_object* v_snd_3726_; lean_object* v_fst_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
v_decls_3721_ = lean_ctor_get(v_lctx_3716_, 1);
v_size_3722_ = lean_ctor_get(v_decls_3721_, 2);
lean_inc(v_size_3722_);
v___x_3723_ = l_Lean_NameSet_empty;
v___x_3724_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_size_3722_, v_lctx_3716_, v___x_3723_, v_a_3717_);
v_fst_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_fst_3725_);
v_snd_3726_ = lean_ctor_get(v___x_3724_, 1);
lean_inc(v_snd_3726_);
lean_dec_ref(v___x_3724_);
v_fst_3727_ = lean_ctor_get(v_fst_3725_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_fst_3725_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; 
v_unused_3735_ = lean_ctor_get(v_fst_3725_, 1);
lean_dec(v_unused_3735_);
v___x_3729_ = v_fst_3725_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_fst_3727_);
lean_dec(v_fst_3725_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 1, v_snd_3726_);
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_fst_3727_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_snd_3726_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(lean_object* v_n_3736_, lean_object* v_i_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___redArg(v_i_3737_, v_a_3739_, v___y_3740_, v___y_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0___boxed(lean_object* v_n_3743_, lean_object* v_i_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_LocalContext_sanitizeNames_spec__0(v_n_3743_, v_i_3744_, v_a_3745_, v_a_3746_, v___y_3747_, v___y_3748_);
lean_dec(v_n_3743_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object* v_lctx_3750_, lean_object* v_fvarId_3751_){
_start:
{
lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___x_3764_; 
lean_inc_ref(v_lctx_3750_);
v___x_3764_ = lean_local_ctx_find(v_lctx_3750_, v_fvarId_3751_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v___x_3765_; 
lean_dec_ref(v_lctx_3750_);
v___x_3765_ = lean_box(0);
return v___x_3765_;
}
else
{
lean_object* v_val_3766_; lean_object* v___y_3768_; lean_object* v_userName_3773_; 
v_val_3766_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_val_3766_);
lean_dec_ref_known(v___x_3764_, 1);
v_userName_3773_ = lean_ctor_get(v_val_3766_, 2);
lean_inc(v_userName_3773_);
v___y_3768_ = v_userName_3773_;
goto v___jp_3767_;
v___jp_3767_:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_3750_, v___y_3768_);
lean_dec_ref(v_lctx_3750_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v___x_3770_; 
lean_dec(v___y_3768_);
lean_dec(v_val_3766_);
v___x_3770_ = lean_box(0);
return v___x_3770_;
}
else
{
lean_object* v_val_3771_; lean_object* v_fvarId_3772_; 
v_val_3771_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_val_3771_);
lean_dec_ref_known(v___x_3769_, 1);
v_fvarId_3772_ = lean_ctor_get(v_val_3766_, 1);
lean_inc(v_fvarId_3772_);
lean_dec(v_val_3766_);
v___y_3760_ = v___y_3768_;
v___y_3761_ = v_val_3771_;
v___y_3762_ = v_fvarId_3772_;
goto v___jp_3759_;
}
}
}
v___jp_3752_:
{
uint8_t v___x_3756_; 
v___x_3756_ = l_Lean_instBEqFVarId_beq(v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec(v___y_3754_);
if (v___x_3756_ == 0)
{
lean_object* v___x_3757_; 
lean_dec(v___y_3753_);
v___x_3757_ = lean_box(0);
return v___x_3757_;
}
else
{
lean_object* v___x_3758_; 
v___x_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3758_, 0, v___y_3753_);
return v___x_3758_;
}
}
v___jp_3759_:
{
lean_object* v_fvarId_3763_; 
v_fvarId_3763_ = lean_ctor_get(v___y_3761_, 1);
lean_inc(v_fvarId_3763_);
lean_dec_ref(v___y_3761_);
v___y_3753_ = v___y_3760_;
v___y_3754_ = v___y_3762_;
v___y_3755_ = v_fvarId_3763_;
goto v___jp_3752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(size_t v_sz_3774_, size_t v_i_3775_, lean_object* v_bs_3776_){
_start:
{
uint8_t v___x_3777_; 
v___x_3777_ = lean_usize_dec_lt(v_i_3775_, v_sz_3774_);
if (v___x_3777_ == 0)
{
return v_bs_3776_;
}
else
{
lean_object* v_v_3778_; lean_object* v_snd_3779_; lean_object* v___x_3780_; lean_object* v_bs_x27_3781_; size_t v___x_3782_; size_t v___x_3783_; lean_object* v___x_3784_; 
v_v_3778_ = lean_array_uget_borrowed(v_bs_3776_, v_i_3775_);
v_snd_3779_ = lean_ctor_get(v_v_3778_, 1);
lean_inc(v_snd_3779_);
v___x_3780_ = lean_unsigned_to_nat(0u);
v_bs_x27_3781_ = lean_array_uset(v_bs_3776_, v_i_3775_, v___x_3780_);
v___x_3782_ = ((size_t)1ULL);
v___x_3783_ = lean_usize_add(v_i_3775_, v___x_3782_);
v___x_3784_ = lean_array_uset(v_bs_x27_3781_, v_i_3775_, v_snd_3779_);
v_i_3775_ = v___x_3783_;
v_bs_3776_ = v___x_3784_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0___boxed(lean_object* v_sz_3786_, lean_object* v_i_3787_, lean_object* v_bs_3788_){
_start:
{
size_t v_sz_boxed_3789_; size_t v_i_boxed_3790_; lean_object* v_res_3791_; 
v_sz_boxed_3789_ = lean_unbox_usize(v_sz_3786_);
lean_dec(v_sz_3786_);
v_i_boxed_3790_ = lean_unbox_usize(v_i_3787_);
lean_dec(v_i_3787_);
v_res_3791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_boxed_3789_, v_i_boxed_3790_, v_bs_3788_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(lean_object* v_lctx_3792_, size_t v_sz_3793_, size_t v_i_3794_, lean_object* v_bs_3795_){
_start:
{
uint8_t v___x_3796_; 
v___x_3796_ = lean_usize_dec_lt(v_i_3794_, v_sz_3793_);
if (v___x_3796_ == 0)
{
return v_bs_3795_;
}
else
{
lean_object* v_fvarIdToDecl_3797_; lean_object* v_v_3798_; lean_object* v___x_3799_; lean_object* v_bs_x27_3800_; lean_object* v___y_3802_; lean_object* v___x_3807_; 
v_fvarIdToDecl_3797_ = lean_ctor_get(v_lctx_3792_, 0);
v_v_3798_ = lean_array_uget(v_bs_3795_, v_i_3794_);
v___x_3799_ = lean_unsigned_to_nat(0u);
v_bs_x27_3800_ = lean_array_uset(v_bs_3795_, v_i_3794_, v___x_3799_);
v___x_3807_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_LocalContext_find_x3f_spec__0___redArg(v_fvarIdToDecl_3797_, v_v_3798_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3799_);
lean_ctor_set(v___x_3808_, 1, v_v_3798_);
v___y_3802_ = v___x_3808_;
goto v___jp_3801_;
}
else
{
lean_object* v_val_3809_; lean_object* v_index_3810_; lean_object* v___x_3811_; 
v_val_3809_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_val_3809_);
lean_dec_ref_known(v___x_3807_, 1);
v_index_3810_ = lean_ctor_get(v_val_3809_, 0);
lean_inc(v_index_3810_);
lean_dec(v_val_3809_);
v___x_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3811_, 0, v_index_3810_);
lean_ctor_set(v___x_3811_, 1, v_v_3798_);
v___y_3802_ = v___x_3811_;
goto v___jp_3801_;
}
v___jp_3801_:
{
size_t v___x_3803_; size_t v___x_3804_; lean_object* v___x_3805_; 
v___x_3803_ = ((size_t)1ULL);
v___x_3804_ = lean_usize_add(v_i_3794_, v___x_3803_);
v___x_3805_ = lean_array_uset(v_bs_x27_3800_, v_i_3794_, v___y_3802_);
v_i_3794_ = v___x_3804_;
v_bs_3795_ = v___x_3805_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1___boxed(lean_object* v_lctx_3812_, lean_object* v_sz_3813_, lean_object* v_i_3814_, lean_object* v_bs_3815_){
_start:
{
size_t v_sz_boxed_3816_; size_t v_i_boxed_3817_; lean_object* v_res_3818_; 
v_sz_boxed_3816_ = lean_unbox_usize(v_sz_3813_);
lean_dec(v_sz_3813_);
v_i_boxed_3817_ = lean_unbox_usize(v_i_3814_);
lean_dec(v_i_3814_);
v_res_3818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3812_, v_sz_boxed_3816_, v_i_boxed_3817_, v_bs_3815_);
lean_dec_ref(v_lctx_3812_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(lean_object* v_hi_3819_, lean_object* v_pivot_3820_, lean_object* v_as_3821_, lean_object* v_i_3822_, lean_object* v_k_3823_){
_start:
{
uint8_t v___x_3824_; 
v___x_3824_ = lean_nat_dec_lt(v_k_3823_, v_hi_3819_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_dec(v_k_3823_);
v___x_3825_ = lean_array_fswap(v_as_3821_, v_i_3822_, v_hi_3819_);
v___x_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3826_, 0, v_i_3822_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
return v___x_3826_;
}
else
{
lean_object* v___x_3827_; lean_object* v_fst_3828_; lean_object* v_fst_3829_; uint8_t v___x_3830_; 
v___x_3827_ = lean_array_fget_borrowed(v_as_3821_, v_k_3823_);
v_fst_3828_ = lean_ctor_get(v___x_3827_, 0);
v_fst_3829_ = lean_ctor_get(v_pivot_3820_, 0);
v___x_3830_ = lean_nat_dec_lt(v_fst_3828_, v_fst_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_unsigned_to_nat(1u);
v___x_3832_ = lean_nat_add(v_k_3823_, v___x_3831_);
lean_dec(v_k_3823_);
v_k_3823_ = v___x_3832_;
goto _start;
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3834_ = lean_array_fswap(v_as_3821_, v_i_3822_, v_k_3823_);
v___x_3835_ = lean_unsigned_to_nat(1u);
v___x_3836_ = lean_nat_add(v_i_3822_, v___x_3835_);
lean_dec(v_i_3822_);
v___x_3837_ = lean_nat_add(v_k_3823_, v___x_3835_);
lean_dec(v_k_3823_);
v_as_3821_ = v___x_3834_;
v_i_3822_ = v___x_3836_;
v_k_3823_ = v___x_3837_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg___boxed(lean_object* v_hi_3839_, lean_object* v_pivot_3840_, lean_object* v_as_3841_, lean_object* v_i_3842_, lean_object* v_k_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3839_, v_pivot_3840_, v_as_3841_, v_i_3842_, v_k_3843_);
lean_dec_ref(v_pivot_3840_);
lean_dec(v_hi_3839_);
return v_res_3844_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(lean_object* v_h_3845_, lean_object* v_i_3846_){
_start:
{
lean_object* v_fst_3847_; lean_object* v_fst_3848_; uint8_t v___x_3849_; 
v_fst_3847_ = lean_ctor_get(v_h_3845_, 0);
v_fst_3848_ = lean_ctor_get(v_i_3846_, 0);
v___x_3849_ = lean_nat_dec_lt(v_fst_3847_, v_fst_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0___boxed(lean_object* v_h_3850_, lean_object* v_i_3851_){
_start:
{
uint8_t v_res_3852_; lean_object* v_r_3853_; 
v_res_3852_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v_h_3850_, v_i_3851_);
lean_dec_ref(v_i_3851_);
lean_dec_ref(v_h_3850_);
v_r_3853_ = lean_box(v_res_3852_);
return v_r_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(lean_object* v_n_3854_, lean_object* v_as_3855_, lean_object* v_lo_3856_, lean_object* v_hi_3857_){
_start:
{
lean_object* v___y_3859_; uint8_t v___x_3869_; 
v___x_3869_ = lean_nat_dec_lt(v_lo_3856_, v_hi_3857_);
if (v___x_3869_ == 0)
{
lean_dec(v_lo_3856_);
return v_as_3855_;
}
else
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v_mid_3872_; lean_object* v___y_3874_; lean_object* v___y_3880_; lean_object* v___x_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; 
v___x_3870_ = lean_nat_add(v_lo_3856_, v_hi_3857_);
v___x_3871_ = lean_unsigned_to_nat(1u);
v_mid_3872_ = lean_nat_shiftr(v___x_3870_, v___x_3871_);
lean_dec(v___x_3870_);
v___x_3885_ = lean_array_fget_borrowed(v_as_3855_, v_mid_3872_);
v___x_3886_ = lean_array_fget_borrowed(v_as_3855_, v_lo_3856_);
v___x_3887_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3885_, v___x_3886_);
if (v___x_3887_ == 0)
{
v___y_3880_ = v_as_3855_;
goto v___jp_3879_;
}
else
{
lean_object* v___x_3888_; 
v___x_3888_ = lean_array_fswap(v_as_3855_, v_lo_3856_, v_mid_3872_);
v___y_3880_ = v___x_3888_;
goto v___jp_3879_;
}
v___jp_3873_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; 
v___x_3875_ = lean_array_fget_borrowed(v___y_3874_, v_mid_3872_);
v___x_3876_ = lean_array_fget_borrowed(v___y_3874_, v_hi_3857_);
v___x_3877_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3875_, v___x_3876_);
if (v___x_3877_ == 0)
{
lean_dec(v_mid_3872_);
v___y_3859_ = v___y_3874_;
goto v___jp_3858_;
}
else
{
lean_object* v___x_3878_; 
v___x_3878_ = lean_array_fswap(v___y_3874_, v_mid_3872_, v_hi_3857_);
lean_dec(v_mid_3872_);
v___y_3859_ = v___x_3878_;
goto v___jp_3858_;
}
}
v___jp_3879_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3881_ = lean_array_fget_borrowed(v___y_3880_, v_hi_3857_);
v___x_3882_ = lean_array_fget_borrowed(v___y_3880_, v_lo_3856_);
v___x_3883_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___lam__0(v___x_3881_, v___x_3882_);
if (v___x_3883_ == 0)
{
v___y_3874_ = v___y_3880_;
goto v___jp_3873_;
}
else
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_array_fswap(v___y_3880_, v_lo_3856_, v_hi_3857_);
v___y_3874_ = v___x_3884_;
goto v___jp_3873_;
}
}
}
v___jp_3858_:
{
lean_object* v_pivot_3860_; lean_object* v___x_3861_; lean_object* v_fst_3862_; lean_object* v_snd_3863_; uint8_t v___x_3864_; 
v_pivot_3860_ = lean_array_fget(v___y_3859_, v_hi_3857_);
lean_inc_n(v_lo_3856_, 2);
v___x_3861_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3857_, v_pivot_3860_, v___y_3859_, v_lo_3856_, v_lo_3856_);
lean_dec(v_pivot_3860_);
v_fst_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_fst_3862_);
v_snd_3863_ = lean_ctor_get(v___x_3861_, 1);
lean_inc(v_snd_3863_);
lean_dec_ref(v___x_3861_);
v___x_3864_ = lean_nat_dec_le(v_hi_3857_, v_fst_3862_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3865_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3854_, v_snd_3863_, v_lo_3856_, v_fst_3862_);
v___x_3866_ = lean_unsigned_to_nat(1u);
v___x_3867_ = lean_nat_add(v_fst_3862_, v___x_3866_);
lean_dec(v_fst_3862_);
v_as_3855_ = v___x_3865_;
v_lo_3856_ = v___x_3867_;
goto _start;
}
else
{
lean_dec(v_fst_3862_);
lean_dec(v_lo_3856_);
return v_snd_3863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg___boxed(lean_object* v_n_3889_, lean_object* v_as_3890_, lean_object* v_lo_3891_, lean_object* v_hi_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3889_, v_as_3890_, v_lo_3891_, v_hi_3892_);
lean_dec(v_hi_3892_);
lean_dec(v_n_3889_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder(lean_object* v_lctx_3894_, lean_object* v_hyps_3895_){
_start:
{
lean_object* v___y_3897_; size_t v_sz_3901_; size_t v___x_3902_; lean_object* v_hyps_3903_; lean_object* v___x_3904_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v_sz_3901_ = lean_array_size(v_hyps_3895_);
v___x_3902_ = ((size_t)0ULL);
v_hyps_3903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__1(v_lctx_3894_, v_sz_3901_, v___x_3902_, v_hyps_3895_);
v___x_3904_ = lean_array_get_size(v_hyps_3903_);
v___x_3909_ = lean_unsigned_to_nat(0u);
v___x_3910_ = lean_nat_dec_eq(v___x_3904_, v___x_3909_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___y_3914_; uint8_t v___x_3916_; 
v___x_3911_ = lean_unsigned_to_nat(1u);
v___x_3912_ = lean_nat_sub(v___x_3904_, v___x_3911_);
v___x_3916_ = lean_nat_dec_le(v___x_3909_, v___x_3912_);
if (v___x_3916_ == 0)
{
lean_inc(v___x_3912_);
v___y_3914_ = v___x_3912_;
goto v___jp_3913_;
}
else
{
v___y_3914_ = v___x_3909_;
goto v___jp_3913_;
}
v___jp_3913_:
{
uint8_t v___x_3915_; 
v___x_3915_ = lean_nat_dec_le(v___y_3914_, v___x_3912_);
if (v___x_3915_ == 0)
{
lean_dec(v___x_3912_);
lean_inc(v___y_3914_);
v___y_3906_ = v___y_3914_;
v___y_3907_ = v___y_3914_;
goto v___jp_3905_;
}
else
{
v___y_3906_ = v___y_3914_;
v___y_3907_ = v___x_3912_;
goto v___jp_3905_;
}
}
}
else
{
v___y_3897_ = v_hyps_3903_;
goto v___jp_3896_;
}
v___jp_3896_:
{
size_t v_sz_3898_; size_t v___x_3899_; lean_object* v___x_3900_; 
v_sz_3898_ = lean_array_size(v___y_3897_);
v___x_3899_ = ((size_t)0ULL);
v___x_3900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__0(v_sz_3898_, v___x_3899_, v___y_3897_);
return v___x_3900_;
}
v___jp_3905_:
{
lean_object* v___x_3908_; 
v___x_3908_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v___x_3904_, v_hyps_3903_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3907_);
v___y_3897_ = v___x_3908_;
goto v___jp_3896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_sortFVarsByContextOrder___boxed(lean_object* v_lctx_3917_, lean_object* v_hyps_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_LocalContext_sortFVarsByContextOrder(v_lctx_3917_, v_hyps_3918_);
lean_dec_ref(v_lctx_3917_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(lean_object* v_n_3920_, lean_object* v_as_3921_, lean_object* v_lo_3922_, lean_object* v_hi_3923_, lean_object* v_w_3924_, lean_object* v_hlo_3925_, lean_object* v_hhi_3926_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___redArg(v_n_3920_, v_as_3921_, v_lo_3922_, v_hi_3923_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2___boxed(lean_object* v_n_3928_, lean_object* v_as_3929_, lean_object* v_lo_3930_, lean_object* v_hi_3931_, lean_object* v_w_3932_, lean_object* v_hlo_3933_, lean_object* v_hhi_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2(v_n_3928_, v_as_3929_, v_lo_3930_, v_hi_3931_, v_w_3932_, v_hlo_3933_, v_hhi_3934_);
lean_dec(v_hi_3931_);
lean_dec(v_n_3928_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(lean_object* v_n_3936_, lean_object* v_lo_3937_, lean_object* v_hi_3938_, lean_object* v_hhi_3939_, lean_object* v_pivot_3940_, lean_object* v_as_3941_, lean_object* v_i_3942_, lean_object* v_k_3943_, lean_object* v_ilo_3944_, lean_object* v_ik_3945_, lean_object* v_w_3946_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___redArg(v_hi_3938_, v_pivot_3940_, v_as_3941_, v_i_3942_, v_k_3943_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2___boxed(lean_object* v_n_3948_, lean_object* v_lo_3949_, lean_object* v_hi_3950_, lean_object* v_hhi_3951_, lean_object* v_pivot_3952_, lean_object* v_as_3953_, lean_object* v_i_3954_, lean_object* v_k_3955_, lean_object* v_ilo_3956_, lean_object* v_ik_3957_, lean_object* v_w_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LocalContext_sortFVarsByContextOrder_spec__2_spec__2(v_n_3948_, v_lo_3949_, v_hi_3950_, v_hhi_3951_, v_pivot_3952_, v_as_3953_, v_i_3954_, v_k_3955_, v_ilo_3956_, v_ik_3957_, v_w_3958_);
lean_dec_ref(v_pivot_3952_);
lean_dec(v_hi_3950_);
lean_dec(v_lo_3949_);
lean_dec(v_n_3948_);
return v_res_3959_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(lean_object* v_a_3960_, lean_object* v_x_3961_){
_start:
{
if (lean_obj_tag(v_x_3961_) == 0)
{
uint8_t v___x_3962_; 
v___x_3962_ = 0;
return v___x_3962_;
}
else
{
lean_object* v_key_3963_; lean_object* v_tail_3964_; uint8_t v___x_3965_; 
v_key_3963_ = lean_ctor_get(v_x_3961_, 0);
v_tail_3964_ = lean_ctor_get(v_x_3961_, 2);
v___x_3965_ = lean_name_eq(v_key_3963_, v_a_3960_);
if (v___x_3965_ == 0)
{
v_x_3961_ = v_tail_3964_;
goto _start;
}
else
{
return v___x_3965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg___boxed(lean_object* v_a_3967_, lean_object* v_x_3968_){
_start:
{
uint8_t v_res_3969_; lean_object* v_r_3970_; 
v_res_3969_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3967_, v_x_3968_);
lean_dec(v_x_3968_);
lean_dec(v_a_3967_);
v_r_3970_ = lean_box(v_res_3969_);
return v_r_3970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(lean_object* v_a_3971_, lean_object* v_x_3972_){
_start:
{
if (lean_obj_tag(v_x_3972_) == 0)
{
return v_x_3972_;
}
else
{
lean_object* v_key_3973_; lean_object* v_value_3974_; lean_object* v_tail_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3984_; 
v_key_3973_ = lean_ctor_get(v_x_3972_, 0);
v_value_3974_ = lean_ctor_get(v_x_3972_, 1);
v_tail_3975_ = lean_ctor_get(v_x_3972_, 2);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_x_3972_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3977_ = v_x_3972_;
v_isShared_3978_ = v_isSharedCheck_3984_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_tail_3975_);
lean_inc(v_value_3974_);
lean_inc(v_key_3973_);
lean_dec(v_x_3972_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3984_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
uint8_t v___x_3979_; 
v___x_3979_ = lean_name_eq(v_key_3973_, v_a_3971_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3982_; 
v___x_3980_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3971_, v_tail_3975_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 2, v___x_3980_);
v___x_3982_ = v___x_3977_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_key_3973_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v_value_3974_);
lean_ctor_set(v_reuseFailAlloc_3983_, 2, v___x_3980_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
else
{
lean_del_object(v___x_3977_);
lean_dec(v_value_3974_);
lean_dec(v_key_3973_);
return v_tail_3975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg___boxed(lean_object* v_a_3985_, lean_object* v_x_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3985_, v_x_3986_);
lean_dec(v_a_3985_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(lean_object* v_m_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_size_3990_; lean_object* v_buckets_3991_; lean_object* v___x_3992_; uint64_t v___y_3994_; 
v_size_3990_ = lean_ctor_get(v_m_3988_, 0);
v_buckets_3991_ = lean_ctor_get(v_m_3988_, 1);
v___x_3992_ = lean_array_get_size(v_buckets_3991_);
if (lean_obj_tag(v_a_3989_) == 0)
{
uint64_t v___x_4023_; 
v___x_4023_ = 1723ULL;
v___y_3994_ = v___x_4023_;
goto v___jp_3993_;
}
else
{
uint64_t v_hash_4024_; 
v_hash_4024_ = lean_ctor_get_uint64(v_a_3989_, sizeof(void*)*2);
v___y_3994_ = v_hash_4024_;
goto v___jp_3993_;
}
v___jp_3993_:
{
uint64_t v___x_3995_; uint64_t v___x_3996_; uint64_t v_fold_3997_; uint64_t v___x_3998_; uint64_t v___x_3999_; uint64_t v___x_4000_; size_t v___x_4001_; size_t v___x_4002_; size_t v___x_4003_; size_t v___x_4004_; size_t v___x_4005_; lean_object* v_bkt_4006_; uint8_t v___x_4007_; 
v___x_3995_ = 32ULL;
v___x_3996_ = lean_uint64_shift_right(v___y_3994_, v___x_3995_);
v_fold_3997_ = lean_uint64_xor(v___y_3994_, v___x_3996_);
v___x_3998_ = 16ULL;
v___x_3999_ = lean_uint64_shift_right(v_fold_3997_, v___x_3998_);
v___x_4000_ = lean_uint64_xor(v_fold_3997_, v___x_3999_);
v___x_4001_ = lean_uint64_to_usize(v___x_4000_);
v___x_4002_ = lean_usize_of_nat(v___x_3992_);
v___x_4003_ = ((size_t)1ULL);
v___x_4004_ = lean_usize_sub(v___x_4002_, v___x_4003_);
v___x_4005_ = lean_usize_land(v___x_4001_, v___x_4004_);
v_bkt_4006_ = lean_array_uget_borrowed(v_buckets_3991_, v___x_4005_);
v___x_4007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_3989_, v_bkt_4006_);
if (v___x_4007_ == 0)
{
return v_m_3988_;
}
else
{
lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4020_; 
lean_inc(v_bkt_4006_);
lean_inc_ref(v_buckets_3991_);
lean_inc(v_size_3990_);
v_isSharedCheck_4020_ = !lean_is_exclusive(v_m_3988_);
if (v_isSharedCheck_4020_ == 0)
{
lean_object* v_unused_4021_; lean_object* v_unused_4022_; 
v_unused_4021_ = lean_ctor_get(v_m_3988_, 1);
lean_dec(v_unused_4021_);
v_unused_4022_ = lean_ctor_get(v_m_3988_, 0);
lean_dec(v_unused_4022_);
v___x_4009_ = v_m_3988_;
v_isShared_4010_ = v_isSharedCheck_4020_;
goto v_resetjp_4008_;
}
else
{
lean_dec(v_m_3988_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4020_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4011_; lean_object* v_buckets_x27_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4018_; 
v___x_4011_ = lean_box(0);
v_buckets_x27_4012_ = lean_array_uset(v_buckets_3991_, v___x_4005_, v___x_4011_);
v___x_4013_ = lean_unsigned_to_nat(1u);
v___x_4014_ = lean_nat_sub(v_size_3990_, v___x_4013_);
lean_dec(v_size_3990_);
v___x_4015_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_3989_, v_bkt_4006_);
v___x_4016_ = lean_array_uset(v_buckets_x27_4012_, v___x_4005_, v___x_4015_);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 1, v___x_4016_);
lean_ctor_set(v___x_4009_, 0, v___x_4014_);
v___x_4018_ = v___x_4009_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4014_);
lean_ctor_set(v_reuseFailAlloc_4019_, 1, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg___boxed(lean_object* v_m_4025_, lean_object* v_a_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4025_, v_a_4026_);
lean_dec(v_a_4026_);
return v_res_4027_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(lean_object* v_m_4028_, lean_object* v_a_4029_){
_start:
{
lean_object* v_buckets_4030_; lean_object* v___x_4031_; uint64_t v___y_4033_; 
v_buckets_4030_ = lean_ctor_get(v_m_4028_, 1);
v___x_4031_ = lean_array_get_size(v_buckets_4030_);
if (lean_obj_tag(v_a_4029_) == 0)
{
uint64_t v___x_4047_; 
v___x_4047_ = 1723ULL;
v___y_4033_ = v___x_4047_;
goto v___jp_4032_;
}
else
{
uint64_t v_hash_4048_; 
v_hash_4048_ = lean_ctor_get_uint64(v_a_4029_, sizeof(void*)*2);
v___y_4033_ = v_hash_4048_;
goto v___jp_4032_;
}
v___jp_4032_:
{
uint64_t v___x_4034_; uint64_t v___x_4035_; uint64_t v_fold_4036_; uint64_t v___x_4037_; uint64_t v___x_4038_; uint64_t v___x_4039_; size_t v___x_4040_; size_t v___x_4041_; size_t v___x_4042_; size_t v___x_4043_; size_t v___x_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; 
v___x_4034_ = 32ULL;
v___x_4035_ = lean_uint64_shift_right(v___y_4033_, v___x_4034_);
v_fold_4036_ = lean_uint64_xor(v___y_4033_, v___x_4035_);
v___x_4037_ = 16ULL;
v___x_4038_ = lean_uint64_shift_right(v_fold_4036_, v___x_4037_);
v___x_4039_ = lean_uint64_xor(v_fold_4036_, v___x_4038_);
v___x_4040_ = lean_uint64_to_usize(v___x_4039_);
v___x_4041_ = lean_usize_of_nat(v___x_4031_);
v___x_4042_ = ((size_t)1ULL);
v___x_4043_ = lean_usize_sub(v___x_4041_, v___x_4042_);
v___x_4044_ = lean_usize_land(v___x_4040_, v___x_4043_);
v___x_4045_ = lean_array_uget_borrowed(v_buckets_4030_, v___x_4044_);
v___x_4046_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4029_, v___x_4045_);
return v___x_4046_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg___boxed(lean_object* v_m_4049_, lean_object* v_a_4050_){
_start:
{
uint8_t v_res_4051_; lean_object* v_r_4052_; 
v_res_4051_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4049_, v_a_4050_);
lean_dec(v_a_4050_);
lean_dec_ref(v_m_4049_);
v_r_4052_ = lean_box(v_res_4051_);
return v_r_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(lean_object* v_start_4053_, lean_object* v_as_4054_, size_t v_i_4055_, size_t v_stop_4056_, lean_object* v_b_4057_){
_start:
{
uint8_t v___x_4058_; 
v___x_4058_ = lean_usize_dec_eq(v_i_4055_, v_stop_4056_);
if (v___x_4058_ == 0)
{
size_t v___x_4059_; size_t v___x_4060_; lean_object* v___x_4061_; 
v___x_4059_ = ((size_t)1ULL);
v___x_4060_ = lean_usize_sub(v_i_4055_, v___x_4059_);
v___x_4061_ = lean_array_uget(v_as_4054_, v___x_4060_);
if (lean_obj_tag(v___x_4061_) == 0)
{
v_i_4055_ = v___x_4060_;
goto _start;
}
else
{
lean_object* v_val_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4097_; 
v_val_4063_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4065_ = v___x_4061_;
v_isShared_4066_ = v_isSharedCheck_4097_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_val_4063_);
lean_dec(v___x_4061_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4097_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v_fst_4067_; lean_object* v_snd_4068_; lean_object* v___y_4070_; lean_object* v___y_4086_; lean_object* v_size_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; 
v_fst_4067_ = lean_ctor_get(v_b_4057_, 0);
v_snd_4068_ = lean_ctor_get(v_b_4057_, 1);
v_size_4092_ = lean_ctor_get(v_fst_4067_, 0);
v___x_4093_ = lean_unsigned_to_nat(0u);
v___x_4094_ = lean_nat_dec_eq(v_size_4092_, v___x_4093_);
if (v___x_4094_ == 0)
{
lean_object* v_index_4095_; 
v_index_4095_ = lean_ctor_get(v_val_4063_, 0);
lean_inc(v_index_4095_);
v___y_4086_ = v_index_4095_;
goto v___jp_4085_;
}
else
{
lean_object* v___x_4096_; 
lean_inc(v_snd_4068_);
lean_del_object(v___x_4065_);
lean_dec(v_val_4063_);
lean_dec_ref(v_b_4057_);
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v_snd_4068_);
return v___x_4096_;
}
v___jp_4069_:
{
uint8_t v___x_4071_; 
v___x_4071_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_fst_4067_, v___y_4070_);
if (v___x_4071_ == 0)
{
lean_dec(v___y_4070_);
lean_dec(v_val_4063_);
v_i_4055_ = v___x_4060_;
goto _start;
}
else
{
lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4082_; 
lean_inc(v_snd_4068_);
lean_inc(v_fst_4067_);
v_isSharedCheck_4082_ = !lean_is_exclusive(v_b_4057_);
if (v_isSharedCheck_4082_ == 0)
{
lean_object* v_unused_4083_; lean_object* v_unused_4084_; 
v_unused_4083_ = lean_ctor_get(v_b_4057_, 1);
lean_dec(v_unused_4083_);
v_unused_4084_ = lean_ctor_get(v_b_4057_, 0);
lean_dec(v_unused_4084_);
v___x_4074_ = v_b_4057_;
v_isShared_4075_ = v_isSharedCheck_4082_;
goto v_resetjp_4073_;
}
else
{
lean_dec(v_b_4057_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4082_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4079_; 
v___x_4076_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_fst_4067_, v___y_4070_);
lean_dec(v___y_4070_);
v___x_4077_ = lean_array_push(v_snd_4068_, v_val_4063_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 1, v___x_4077_);
lean_ctor_set(v___x_4074_, 0, v___x_4076_);
v___x_4079_ = v___x_4074_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4076_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
v_i_4055_ = v___x_4060_;
v_b_4057_ = v___x_4079_;
goto _start;
}
}
}
}
v___jp_4085_:
{
uint8_t v___x_4087_; 
v___x_4087_ = lean_nat_dec_lt(v___y_4086_, v_start_4053_);
lean_dec(v___y_4086_);
if (v___x_4087_ == 0)
{
lean_object* v_userName_4088_; 
lean_del_object(v___x_4065_);
v_userName_4088_ = lean_ctor_get(v_val_4063_, 2);
lean_inc(v_userName_4088_);
v___y_4070_ = v_userName_4088_;
goto v___jp_4069_;
}
else
{
lean_object* v___x_4090_; 
lean_inc(v_snd_4068_);
lean_dec(v_val_4063_);
lean_dec_ref(v_b_4057_);
if (v_isShared_4066_ == 0)
{
lean_ctor_set_tag(v___x_4065_, 0);
lean_ctor_set(v___x_4065_, 0, v_snd_4068_);
v___x_4090_ = v___x_4065_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_snd_4068_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
}
}
else
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4098_, 0, v_b_4057_);
return v___x_4098_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_start_4099_, lean_object* v_as_4100_, lean_object* v_i_4101_, lean_object* v_stop_4102_, lean_object* v_b_4103_){
_start:
{
size_t v_i_boxed_4104_; size_t v_stop_boxed_4105_; lean_object* v_res_4106_; 
v_i_boxed_4104_ = lean_unbox_usize(v_i_4101_);
lean_dec(v_i_4101_);
v_stop_boxed_4105_ = lean_unbox_usize(v_stop_4102_);
lean_dec(v_stop_4102_);
v_res_4106_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4099_, v_as_4100_, v_i_boxed_4104_, v_stop_boxed_4105_, v_b_4103_);
lean_dec_ref(v_as_4100_);
lean_dec(v_start_4099_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(lean_object* v_start_4107_, lean_object* v_x_4108_, lean_object* v_x_4109_){
_start:
{
if (lean_obj_tag(v_x_4108_) == 0)
{
lean_object* v_cs_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4123_; 
v_cs_4110_ = lean_ctor_get(v_x_4108_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v_x_4108_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4112_ = v_x_4108_;
v_isShared_4113_ = v_isSharedCheck_4123_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_cs_4110_);
lean_dec(v_x_4108_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4123_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; 
v___x_4114_ = lean_array_get_size(v_cs_4110_);
v___x_4115_ = lean_unsigned_to_nat(0u);
v___x_4116_ = lean_nat_dec_lt(v___x_4115_, v___x_4114_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4118_; 
lean_dec_ref(v_cs_4110_);
if (v_isShared_4113_ == 0)
{
lean_ctor_set_tag(v___x_4112_, 1);
lean_ctor_set(v___x_4112_, 0, v_x_4109_);
v___x_4118_ = v___x_4112_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_x_4109_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
else
{
size_t v___x_4120_; size_t v___x_4121_; lean_object* v___x_4122_; 
lean_del_object(v___x_4112_);
v___x_4120_ = lean_usize_of_nat(v___x_4114_);
v___x_4121_ = ((size_t)0ULL);
v___x_4122_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4107_, v_cs_4110_, v___x_4120_, v___x_4121_, v_x_4109_);
lean_dec_ref(v_cs_4110_);
return v___x_4122_;
}
}
}
else
{
lean_object* v_vs_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4137_; 
v_vs_4124_ = lean_ctor_get(v_x_4108_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v_x_4108_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4126_ = v_x_4108_;
v_isShared_4127_ = v_isSharedCheck_4137_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_vs_4124_);
lean_dec(v_x_4108_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4137_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; uint8_t v___x_4130_; 
v___x_4128_ = lean_array_get_size(v_vs_4124_);
v___x_4129_ = lean_unsigned_to_nat(0u);
v___x_4130_ = lean_nat_dec_lt(v___x_4129_, v___x_4128_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4132_; 
lean_dec_ref(v_vs_4124_);
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 0, v_x_4109_);
v___x_4132_ = v___x_4126_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_x_4109_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
else
{
size_t v___x_4134_; size_t v___x_4135_; lean_object* v___x_4136_; 
lean_del_object(v___x_4126_);
v___x_4134_ = lean_usize_of_nat(v___x_4128_);
v___x_4135_ = ((size_t)0ULL);
v___x_4136_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4107_, v_vs_4124_, v___x_4134_, v___x_4135_, v_x_4109_);
lean_dec_ref(v_vs_4124_);
return v___x_4136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_start_4138_, lean_object* v_as_4139_, size_t v_i_4140_, size_t v_stop_4141_, lean_object* v_b_4142_){
_start:
{
uint8_t v___x_4143_; 
v___x_4143_ = lean_usize_dec_eq(v_i_4140_, v_stop_4141_);
if (v___x_4143_ == 0)
{
size_t v___x_4144_; size_t v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4144_ = ((size_t)1ULL);
v___x_4145_ = lean_usize_sub(v_i_4140_, v___x_4144_);
v___x_4146_ = lean_array_uget_borrowed(v_as_4139_, v___x_4145_);
lean_inc(v___x_4146_);
v___x_4147_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4138_, v___x_4146_, v_b_4142_);
if (lean_obj_tag(v___x_4147_) == 0)
{
return v___x_4147_;
}
else
{
lean_object* v_a_4148_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4147_, 1);
v_i_4140_ = v___x_4145_;
v_b_4142_ = v_a_4148_;
goto _start;
}
}
else
{
lean_object* v___x_4150_; 
v___x_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4150_, 0, v_b_4142_);
return v___x_4150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_start_4151_, lean_object* v_as_4152_, lean_object* v_i_4153_, lean_object* v_stop_4154_, lean_object* v_b_4155_){
_start:
{
size_t v_i_boxed_4156_; size_t v_stop_boxed_4157_; lean_object* v_res_4158_; 
v_i_boxed_4156_ = lean_unbox_usize(v_i_4153_);
lean_dec(v_i_4153_);
v_stop_boxed_4157_ = lean_unbox_usize(v_stop_4154_);
lean_dec(v_stop_4154_);
v_res_4158_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4151_, v_as_4152_, v_i_boxed_4156_, v_stop_boxed_4157_, v_b_4155_);
lean_dec_ref(v_as_4152_);
lean_dec(v_start_4151_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_start_4159_, lean_object* v_x_4160_, lean_object* v_x_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4159_, v_x_4160_, v_x_4161_);
lean_dec(v_start_4159_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(lean_object* v_start_4163_, lean_object* v_t_4164_, lean_object* v_init_4165_){
_start:
{
lean_object* v_root_4166_; lean_object* v_tail_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
v_root_4166_ = lean_ctor_get(v_t_4164_, 0);
lean_inc_ref(v_root_4166_);
v_tail_4167_ = lean_ctor_get(v_t_4164_, 1);
lean_inc_ref(v_tail_4167_);
lean_dec_ref(v_t_4164_);
v___x_4168_ = lean_array_get_size(v_tail_4167_);
v___x_4169_ = lean_unsigned_to_nat(0u);
v___x_4170_ = lean_nat_dec_lt(v___x_4169_, v___x_4168_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; 
lean_dec_ref(v_tail_4167_);
v___x_4171_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4163_, v_root_4166_, v_init_4165_);
return v___x_4171_;
}
else
{
size_t v___x_4172_; size_t v___x_4173_; lean_object* v___x_4174_; 
v___x_4172_ = lean_usize_of_nat(v___x_4168_);
v___x_4173_ = ((size_t)0ULL);
v___x_4174_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4163_, v_tail_4167_, v___x_4172_, v___x_4173_, v_init_4165_);
lean_dec_ref(v_tail_4167_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_dec_ref(v_root_4166_);
return v___x_4174_;
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4176_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4175_);
lean_dec_ref_known(v___x_4174_, 1);
v___x_4176_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4163_, v_root_4166_, v_a_4175_);
return v___x_4176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg___boxed(lean_object* v_start_4177_, lean_object* v_t_4178_, lean_object* v_init_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4177_, v_t_4178_, v_init_4179_);
lean_dec(v_start_4177_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(lean_object* v_start_4181_, lean_object* v_lctx_4182_, lean_object* v_init_4183_){
_start:
{
lean_object* v_decls_4184_; lean_object* v___x_4185_; 
v_decls_4184_ = lean_ctor_get(v_lctx_4182_, 1);
lean_inc_ref(v_decls_4184_);
lean_dec_ref(v_lctx_4182_);
v___x_4185_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4181_, v_decls_4184_, v_init_4183_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg___boxed(lean_object* v_start_4186_, lean_object* v_lctx_4187_, lean_object* v_init_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4186_, v_lctx_4187_, v_init_4188_);
lean_dec(v_start_4186_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg(lean_object* v_lctx_4192_, lean_object* v_userNames_4193_, lean_object* v_start_4194_){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4195_ = ((lean_object*)(l_Lean_LocalContext_findFromUserNames___redArg___closed__0));
v___x_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4196_, 0, v_userNames_4193_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4194_, v_lctx_4192_, v___x_4196_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4199_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref_known(v___x_4197_, 1);
v___x_4199_ = l_Array_reverse___redArg(v_a_4198_);
return v___x_4199_;
}
else
{
lean_object* v_a_4200_; lean_object* v_snd_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_a_4200_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4197_, 1);
v_snd_4201_ = lean_ctor_get(v_a_4200_, 1);
lean_inc(v_snd_4201_);
lean_dec(v_a_4200_);
v___x_4202_ = l_Array_reverse___redArg(v_snd_4201_);
v___x_4203_ = l_Array_reverse___redArg(v___x_4202_);
return v___x_4203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___redArg___boxed(lean_object* v_lctx_4204_, lean_object* v_userNames_4205_, lean_object* v_start_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4204_, v_userNames_4205_, v_start_4206_);
lean_dec(v_start_4206_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames(lean_object* v_00_u03b1_4208_, lean_object* v_lctx_4209_, lean_object* v_userNames_4210_, lean_object* v_start_4211_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Lean_LocalContext_findFromUserNames___redArg(v_lctx_4209_, v_userNames_4210_, v_start_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findFromUserNames___boxed(lean_object* v_00_u03b1_4213_, lean_object* v_lctx_4214_, lean_object* v_userNames_4215_, lean_object* v_start_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Lean_LocalContext_findFromUserNames(v_00_u03b1_4213_, v_lctx_4214_, v_userNames_4215_, v_start_4216_);
lean_dec(v_start_4216_);
return v_res_4217_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(lean_object* v_00_u03b2_4218_, lean_object* v_m_4219_, lean_object* v_a_4220_){
_start:
{
uint8_t v___x_4221_; 
v___x_4221_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___redArg(v_m_4219_, v_a_4220_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0___boxed(lean_object* v_00_u03b2_4222_, lean_object* v_m_4223_, lean_object* v_a_4224_){
_start:
{
uint8_t v_res_4225_; lean_object* v_r_4226_; 
v_res_4225_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0(v_00_u03b2_4222_, v_m_4223_, v_a_4224_);
lean_dec(v_a_4224_);
lean_dec_ref(v_m_4223_);
v_r_4226_ = lean_box(v_res_4225_);
return v_r_4226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(lean_object* v_00_u03b2_4227_, lean_object* v_m_4228_, lean_object* v_a_4229_){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___redArg(v_m_4228_, v_a_4229_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1___boxed(lean_object* v_00_u03b2_4231_, lean_object* v_m_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1(v_00_u03b2_4231_, v_m_4232_, v_a_4233_);
lean_dec(v_a_4233_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(lean_object* v_00_u03b1_4235_, lean_object* v_start_4236_, lean_object* v_lctx_4237_, lean_object* v_init_4238_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___redArg(v_start_4236_, v_lctx_4237_, v_init_4238_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2___boxed(lean_object* v_00_u03b1_4240_, lean_object* v_start_4241_, lean_object* v_lctx_4242_, lean_object* v_init_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2(v_00_u03b1_4240_, v_start_4241_, v_lctx_4242_, v_init_4243_);
lean_dec(v_start_4241_);
return v_res_4244_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(lean_object* v_00_u03b2_4245_, lean_object* v_a_4246_, lean_object* v_x_4247_){
_start:
{
uint8_t v___x_4248_; 
v___x_4248_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___redArg(v_a_4246_, v_x_4247_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4249_, lean_object* v_a_4250_, lean_object* v_x_4251_){
_start:
{
uint8_t v_res_4252_; lean_object* v_r_4253_; 
v_res_4252_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_LocalContext_findFromUserNames_spec__0_spec__0(v_00_u03b2_4249_, v_a_4250_, v_x_4251_);
lean_dec(v_x_4251_);
lean_dec(v_a_4250_);
v_r_4253_ = lean_box(v_res_4252_);
return v_r_4253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(lean_object* v_00_u03b2_4254_, lean_object* v_a_4255_, lean_object* v_x_4256_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___redArg(v_a_4255_, v_x_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2___boxed(lean_object* v_00_u03b2_4258_, lean_object* v_a_4259_, lean_object* v_x_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_LocalContext_findFromUserNames_spec__1_spec__2(v_00_u03b2_4258_, v_a_4259_, v_x_4260_);
lean_dec(v_a_4259_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(lean_object* v_00_u03b1_4262_, lean_object* v_start_4263_, lean_object* v_t_4264_, lean_object* v_init_4265_){
_start:
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___redArg(v_start_4263_, v_t_4264_, v_init_4265_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4267_, lean_object* v_start_4268_, lean_object* v_t_4269_, lean_object* v_init_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4(v_00_u03b1_4267_, v_start_4268_, v_t_4269_, v_init_4270_);
lean_dec(v_start_4268_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_4272_, lean_object* v_start_4273_, lean_object* v_x_4274_, lean_object* v_x_4275_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___redArg(v_start_4273_, v_x_4274_, v_x_4275_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4277_, lean_object* v_start_4278_, lean_object* v_x_4279_, lean_object* v_x_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5(v_00_u03b1_4277_, v_start_4278_, v_x_4279_, v_x_4280_);
lean_dec(v_start_4278_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_4282_, lean_object* v_start_4283_, lean_object* v_as_4284_, size_t v_i_4285_, size_t v_stop_4286_, lean_object* v_b_4287_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___redArg(v_start_4283_, v_as_4284_, v_i_4285_, v_stop_4286_, v_b_4287_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4289_, lean_object* v_start_4290_, lean_object* v_as_4291_, lean_object* v_i_4292_, lean_object* v_stop_4293_, lean_object* v_b_4294_){
_start:
{
size_t v_i_boxed_4295_; size_t v_stop_boxed_4296_; lean_object* v_res_4297_; 
v_i_boxed_4295_ = lean_unbox_usize(v_i_4292_);
lean_dec(v_i_4292_);
v_stop_boxed_4296_ = lean_unbox_usize(v_stop_4293_);
lean_dec(v_stop_4293_);
v_res_4297_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__6(v_00_u03b1_4289_, v_start_4290_, v_as_4291_, v_i_boxed_4295_, v_stop_boxed_4296_, v_b_4294_);
lean_dec_ref(v_as_4291_);
lean_dec(v_start_4290_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b1_4298_, lean_object* v_start_4299_, lean_object* v_as_4300_, size_t v_i_4301_, size_t v_stop_4302_, lean_object* v_b_4303_){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___redArg(v_start_4299_, v_as_4300_, v_i_4301_, v_stop_4302_, v_b_4303_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4305_, lean_object* v_start_4306_, lean_object* v_as_4307_, lean_object* v_i_4308_, lean_object* v_stop_4309_, lean_object* v_b_4310_){
_start:
{
size_t v_i_boxed_4311_; size_t v_stop_boxed_4312_; lean_object* v_res_4313_; 
v_i_boxed_4311_ = lean_unbox_usize(v_i_4308_);
lean_dec(v_i_4308_);
v_stop_boxed_4312_ = lean_unbox_usize(v_stop_4309_);
lean_dec(v_stop_4309_);
v_res_4313_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_LocalContext_findFromUserNames_spec__2_spec__4_spec__5_spec__6(v_00_u03b1_4305_, v_start_4306_, v_as_4307_, v_i_boxed_4311_, v_stop_boxed_4312_, v_b_4310_);
lean_dec_ref(v_as_4307_);
lean_dec(v_start_4306_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift___redArg(lean_object* v_inst_4314_, lean_object* v_inst_4315_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = lean_apply_2(v_inst_4314_, lean_box(0), v_inst_4315_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLCtxOfMonadLift(lean_object* v_m_4317_, lean_object* v_n_4318_, lean_object* v_inst_4319_, lean_object* v_inst_4320_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = lean_apply_2(v_inst_4319_, lean_box(0), v_inst_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__0(lean_object* v_toPure_4322_, lean_object* v_d_x3f_4323_, lean_object* v_b_4324_){
_start:
{
if (lean_obj_tag(v_d_x3f_4323_) == 0)
{
lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4325_, 0, v_b_4324_);
v___x_4326_ = lean_apply_2(v_toPure_4322_, lean_box(0), v___x_4325_);
return v___x_4326_;
}
else
{
lean_object* v_val_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4342_; 
v_val_4327_ = lean_ctor_get(v_d_x3f_4323_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v_d_x3f_4323_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4329_ = v_d_x3f_4323_;
v_isShared_4330_ = v_isSharedCheck_4342_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_val_4327_);
lean_dec(v_d_x3f_4323_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4342_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
uint8_t v___x_4331_; 
v___x_4331_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4327_);
if (v___x_4331_ == 0)
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4335_; 
v___x_4332_ = l_Lean_LocalDecl_toExpr(v_val_4327_);
v___x_4333_ = lean_array_push(v_b_4324_, v___x_4332_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v___x_4333_);
v___x_4335_ = v___x_4329_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4333_);
v___x_4335_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4336_; 
v___x_4336_ = lean_apply_2(v_toPure_4322_, lean_box(0), v___x_4335_);
return v___x_4336_;
}
}
else
{
lean_object* v___x_4339_; 
lean_dec(v_val_4327_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v_b_4324_);
v___x_4339_ = v___x_4329_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_b_4324_);
v___x_4339_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4340_; 
v___x_4340_ = lean_apply_2(v_toPure_4322_, lean_box(0), v___x_4339_);
return v___x_4340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__1(lean_object* v_toPure_4343_, lean_object* v_____s_4344_){
_start:
{
lean_object* v___x_4345_; 
v___x_4345_ = lean_apply_2(v_toPure_4343_, lean_box(0), v_____s_4344_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2(lean_object* v_inst_4346_, lean_object* v_hs_4347_, lean_object* v___f_4348_, lean_object* v_toBind_4349_, lean_object* v___f_4350_, lean_object* v_____do__lift_4351_){
_start:
{
lean_object* v_decls_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v_decls_4352_ = lean_ctor_get(v_____do__lift_4351_, 1);
v___x_4353_ = l_Lean_PersistentArray_forIn___redArg(v_inst_4346_, v_decls_4352_, v_hs_4347_, v___f_4348_);
v___x_4354_ = lean_apply_4(v_toBind_4349_, lean_box(0), lean_box(0), v___x_4353_, v___f_4350_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg___lam__2___boxed(lean_object* v_inst_4355_, lean_object* v_hs_4356_, lean_object* v___f_4357_, lean_object* v_toBind_4358_, lean_object* v___f_4359_, lean_object* v_____do__lift_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Lean_getLocalHyps___redArg___lam__2(v_inst_4355_, v_hs_4356_, v___f_4357_, v_toBind_4358_, v___f_4359_, v_____do__lift_4360_);
lean_dec_ref(v_____do__lift_4360_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___redArg(lean_object* v_inst_4364_, lean_object* v_inst_4365_){
_start:
{
lean_object* v_toApplicative_4366_; lean_object* v_toBind_4367_; lean_object* v_toPure_4368_; lean_object* v_hs_4369_; lean_object* v___f_4370_; lean_object* v___f_4371_; lean_object* v___f_4372_; lean_object* v___x_4373_; 
v_toApplicative_4366_ = lean_ctor_get(v_inst_4364_, 0);
v_toBind_4367_ = lean_ctor_get(v_inst_4364_, 1);
lean_inc_n(v_toBind_4367_, 2);
v_toPure_4368_ = lean_ctor_get(v_toApplicative_4366_, 1);
v_hs_4369_ = ((lean_object*)(l_Lean_getLocalHyps___redArg___closed__0));
lean_inc_n(v_toPure_4368_, 2);
v___f_4370_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__0), 3, 1);
lean_closure_set(v___f_4370_, 0, v_toPure_4368_);
v___f_4371_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4371_, 0, v_toPure_4368_);
v___f_4372_ = lean_alloc_closure((void*)(l_Lean_getLocalHyps___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_4372_, 0, v_inst_4364_);
lean_closure_set(v___f_4372_, 1, v_hs_4369_);
lean_closure_set(v___f_4372_, 2, v___f_4370_);
lean_closure_set(v___f_4372_, 3, v_toBind_4367_);
lean_closure_set(v___f_4372_, 4, v___f_4371_);
v___x_4373_ = lean_apply_4(v_toBind_4367_, lean_box(0), lean_box(0), v_inst_4365_, v___f_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps(lean_object* v_m_4374_, lean_object* v_inst_4375_, lean_object* v_inst_4376_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Lean_getLocalHyps___redArg(v_inst_4375_, v_inst_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId(lean_object* v_fvarId_4378_, lean_object* v_e_4379_, lean_object* v_d_4380_){
_start:
{
lean_object* v___y_4382_; lean_object* v_fvarId_4414_; 
v_fvarId_4414_ = lean_ctor_get(v_d_4380_, 1);
lean_inc(v_fvarId_4414_);
v___y_4382_ = v_fvarId_4414_;
goto v___jp_4381_;
v___jp_4381_:
{
uint8_t v___x_4383_; 
v___x_4383_ = l_Lean_instBEqFVarId_beq(v___y_4382_, v_fvarId_4378_);
lean_dec(v___y_4382_);
if (v___x_4383_ == 0)
{
if (lean_obj_tag(v_d_4380_) == 0)
{
lean_object* v_index_4384_; lean_object* v_fvarId_4385_; lean_object* v_userName_4386_; lean_object* v_type_4387_; uint8_t v_bi_4388_; uint8_t v_kind_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4397_; 
v_index_4384_ = lean_ctor_get(v_d_4380_, 0);
v_fvarId_4385_ = lean_ctor_get(v_d_4380_, 1);
v_userName_4386_ = lean_ctor_get(v_d_4380_, 2);
v_type_4387_ = lean_ctor_get(v_d_4380_, 3);
v_bi_4388_ = lean_ctor_get_uint8(v_d_4380_, sizeof(void*)*4);
v_kind_4389_ = lean_ctor_get_uint8(v_d_4380_, sizeof(void*)*4 + 1);
v_isSharedCheck_4397_ = !lean_is_exclusive(v_d_4380_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4391_ = v_d_4380_;
v_isShared_4392_ = v_isSharedCheck_4397_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_type_4387_);
lean_inc(v_userName_4386_);
lean_inc(v_fvarId_4385_);
lean_inc(v_index_4384_);
lean_dec(v_d_4380_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4397_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4393_ = l_Lean_Expr_replaceFVarId(v_type_4387_, v_fvarId_4378_, v_e_4379_);
lean_dec_ref(v_type_4387_);
if (v_isShared_4392_ == 0)
{
lean_ctor_set(v___x_4391_, 3, v___x_4393_);
v___x_4395_ = v___x_4391_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_index_4384_);
lean_ctor_set(v_reuseFailAlloc_4396_, 1, v_fvarId_4385_);
lean_ctor_set(v_reuseFailAlloc_4396_, 2, v_userName_4386_);
lean_ctor_set(v_reuseFailAlloc_4396_, 3, v___x_4393_);
lean_ctor_set_uint8(v_reuseFailAlloc_4396_, sizeof(void*)*4, v_bi_4388_);
lean_ctor_set_uint8(v_reuseFailAlloc_4396_, sizeof(void*)*4 + 1, v_kind_4389_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
else
{
lean_object* v_index_4398_; lean_object* v_fvarId_4399_; lean_object* v_userName_4400_; lean_object* v_type_4401_; lean_object* v_value_4402_; uint8_t v_nondep_4403_; uint8_t v_kind_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4413_; 
v_index_4398_ = lean_ctor_get(v_d_4380_, 0);
v_fvarId_4399_ = lean_ctor_get(v_d_4380_, 1);
v_userName_4400_ = lean_ctor_get(v_d_4380_, 2);
v_type_4401_ = lean_ctor_get(v_d_4380_, 3);
v_value_4402_ = lean_ctor_get(v_d_4380_, 4);
v_nondep_4403_ = lean_ctor_get_uint8(v_d_4380_, sizeof(void*)*5);
v_kind_4404_ = lean_ctor_get_uint8(v_d_4380_, sizeof(void*)*5 + 1);
v_isSharedCheck_4413_ = !lean_is_exclusive(v_d_4380_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4406_ = v_d_4380_;
v_isShared_4407_ = v_isSharedCheck_4413_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_value_4402_);
lean_inc(v_type_4401_);
lean_inc(v_userName_4400_);
lean_inc(v_fvarId_4399_);
lean_inc(v_index_4398_);
lean_dec(v_d_4380_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4413_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4411_; 
lean_inc(v_fvarId_4378_);
v___x_4408_ = l_Lean_Expr_replaceFVarId(v_type_4401_, v_fvarId_4378_, v_e_4379_);
lean_dec_ref(v_type_4401_);
v___x_4409_ = l_Lean_Expr_replaceFVarId(v_value_4402_, v_fvarId_4378_, v_e_4379_);
lean_dec_ref(v_value_4402_);
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 4, v___x_4409_);
lean_ctor_set(v___x_4406_, 3, v___x_4408_);
v___x_4411_ = v___x_4406_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_index_4398_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v_fvarId_4399_);
lean_ctor_set(v_reuseFailAlloc_4412_, 2, v_userName_4400_);
lean_ctor_set(v_reuseFailAlloc_4412_, 3, v___x_4408_);
lean_ctor_set(v_reuseFailAlloc_4412_, 4, v___x_4409_);
lean_ctor_set_uint8(v_reuseFailAlloc_4412_, sizeof(void*)*5, v_nondep_4403_);
lean_ctor_set_uint8(v_reuseFailAlloc_4412_, sizeof(void*)*5 + 1, v_kind_4404_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
else
{
lean_dec(v_fvarId_4378_);
return v_d_4380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_replaceFVarId___boxed(lean_object* v_fvarId_4415_, lean_object* v_e_4416_, lean_object* v_d_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4415_, v_e_4416_, v_d_4417_);
lean_dec_ref(v_e_4416_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0(lean_object* v_fvarId_4419_, lean_object* v_e_4420_, lean_object* v_x_4421_){
_start:
{
lean_object* v___x_4422_; 
v___x_4422_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4419_, v_e_4420_, v_x_4421_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId___lam__0___boxed(lean_object* v_fvarId_4423_, lean_object* v_e_4424_, lean_object* v_x_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_LocalContext_replaceFVarId___lam__0(v_fvarId_4423_, v_e_4424_, v_x_4425_);
lean_dec_ref(v_e_4424_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(lean_object* v_fvarId_4427_, lean_object* v_e_4428_, size_t v_sz_4429_, size_t v_i_4430_, lean_object* v_bs_4431_){
_start:
{
uint8_t v___x_4432_; 
v___x_4432_ = lean_usize_dec_lt(v_i_4430_, v_sz_4429_);
if (v___x_4432_ == 0)
{
lean_dec(v_fvarId_4427_);
return v_bs_4431_;
}
else
{
lean_object* v_v_4433_; lean_object* v___x_4434_; lean_object* v_bs_x27_4435_; lean_object* v___y_4437_; 
v_v_4433_ = lean_array_uget(v_bs_4431_, v_i_4430_);
v___x_4434_ = lean_unsigned_to_nat(0u);
v_bs_x27_4435_ = lean_array_uset(v_bs_4431_, v_i_4430_, v___x_4434_);
if (lean_obj_tag(v_v_4433_) == 0)
{
v___y_4437_ = v_v_4433_;
goto v___jp_4436_;
}
else
{
lean_object* v_val_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4450_; 
v_val_4442_ = lean_ctor_get(v_v_4433_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v_v_4433_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4444_ = v_v_4433_;
v_isShared_4445_ = v_isSharedCheck_4450_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_val_4442_);
lean_dec(v_v_4433_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4450_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4446_; lean_object* v___x_4448_; 
lean_inc(v_fvarId_4427_);
v___x_4446_ = l_Lean_LocalDecl_replaceFVarId(v_fvarId_4427_, v_e_4428_, v_val_4442_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 0, v___x_4446_);
v___x_4448_ = v___x_4444_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
v___y_4437_ = v___x_4448_;
goto v___jp_4436_;
}
}
}
v___jp_4436_:
{
size_t v___x_4438_; size_t v___x_4439_; lean_object* v___x_4440_; 
v___x_4438_ = ((size_t)1ULL);
v___x_4439_ = lean_usize_add(v_i_4430_, v___x_4438_);
v___x_4440_ = lean_array_uset(v_bs_x27_4435_, v_i_4430_, v___y_4437_);
v_i_4430_ = v___x_4439_;
v_bs_4431_ = v___x_4440_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3___boxed(lean_object* v_fvarId_4451_, lean_object* v_e_4452_, lean_object* v_sz_4453_, lean_object* v_i_4454_, lean_object* v_bs_4455_){
_start:
{
size_t v_sz_boxed_4456_; size_t v_i_boxed_4457_; lean_object* v_res_4458_; 
v_sz_boxed_4456_ = lean_unbox_usize(v_sz_4453_);
lean_dec(v_sz_4453_);
v_i_boxed_4457_ = lean_unbox_usize(v_i_4454_);
lean_dec(v_i_4454_);
v_res_4458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4451_, v_e_4452_, v_sz_boxed_4456_, v_i_boxed_4457_, v_bs_4455_);
lean_dec_ref(v_e_4452_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(lean_object* v_fvarId_4459_, lean_object* v_e_4460_, size_t v_sz_4461_, size_t v_i_4462_, lean_object* v_bs_4463_){
_start:
{
uint8_t v___x_4464_; 
v___x_4464_ = lean_usize_dec_lt(v_i_4462_, v_sz_4461_);
if (v___x_4464_ == 0)
{
lean_dec(v_fvarId_4459_);
return v_bs_4463_;
}
else
{
lean_object* v_v_4465_; lean_object* v___x_4466_; lean_object* v_bs_x27_4467_; lean_object* v___x_4468_; size_t v___x_4469_; size_t v___x_4470_; lean_object* v___x_4471_; 
v_v_4465_ = lean_array_uget(v_bs_4463_, v_i_4462_);
v___x_4466_ = lean_unsigned_to_nat(0u);
v_bs_x27_4467_ = lean_array_uset(v_bs_4463_, v_i_4462_, v___x_4466_);
lean_inc(v_fvarId_4459_);
v___x_4468_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4459_, v_e_4460_, v_v_4465_);
v___x_4469_ = ((size_t)1ULL);
v___x_4470_ = lean_usize_add(v_i_4462_, v___x_4469_);
v___x_4471_ = lean_array_uset(v_bs_x27_4467_, v_i_4462_, v___x_4468_);
v_i_4462_ = v___x_4470_;
v_bs_4463_ = v___x_4471_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(lean_object* v_fvarId_4473_, lean_object* v_e_4474_, lean_object* v_x_4475_){
_start:
{
if (lean_obj_tag(v_x_4475_) == 0)
{
lean_object* v_cs_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4486_; 
v_cs_4476_ = lean_ctor_get(v_x_4475_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v_x_4475_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4478_ = v_x_4475_;
v_isShared_4479_ = v_isSharedCheck_4486_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_cs_4476_);
lean_dec(v_x_4475_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4486_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
size_t v_sz_4480_; size_t v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4484_; 
v_sz_4480_ = lean_array_size(v_cs_4476_);
v___x_4481_ = ((size_t)0ULL);
v___x_4482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4473_, v_e_4474_, v_sz_4480_, v___x_4481_, v_cs_4476_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 0, v___x_4482_);
v___x_4484_ = v___x_4478_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4482_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
else
{
lean_object* v_vs_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4497_; 
v_vs_4487_ = lean_ctor_get(v_x_4475_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v_x_4475_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4489_ = v_x_4475_;
v_isShared_4490_ = v_isSharedCheck_4497_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_vs_4487_);
lean_dec(v_x_4475_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4497_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
size_t v_sz_4491_; size_t v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4495_; 
v_sz_4491_ = lean_array_size(v_vs_4487_);
v___x_4492_ = ((size_t)0ULL);
v___x_4493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4473_, v_e_4474_, v_sz_4491_, v___x_4492_, v_vs_4487_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 0, v___x_4493_);
v___x_4495_ = v___x_4489_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2___boxed(lean_object* v_fvarId_4498_, lean_object* v_e_4499_, lean_object* v_x_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4498_, v_e_4499_, v_x_4500_);
lean_dec_ref(v_e_4499_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4___boxed(lean_object* v_fvarId_4502_, lean_object* v_e_4503_, lean_object* v_sz_4504_, lean_object* v_i_4505_, lean_object* v_bs_4506_){
_start:
{
size_t v_sz_boxed_4507_; size_t v_i_boxed_4508_; lean_object* v_res_4509_; 
v_sz_boxed_4507_ = lean_unbox_usize(v_sz_4504_);
lean_dec(v_sz_4504_);
v_i_boxed_4508_ = lean_unbox_usize(v_i_4505_);
lean_dec(v_i_4505_);
v_res_4509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2_spec__4(v_fvarId_4502_, v_e_4503_, v_sz_boxed_4507_, v_i_boxed_4508_, v_bs_4506_);
lean_dec_ref(v_e_4503_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(lean_object* v_fvarId_4510_, lean_object* v_e_4511_, lean_object* v_t_4512_){
_start:
{
lean_object* v_root_4513_; lean_object* v_tail_4514_; lean_object* v_size_4515_; size_t v_shift_4516_; lean_object* v_tailOff_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4528_; 
v_root_4513_ = lean_ctor_get(v_t_4512_, 0);
v_tail_4514_ = lean_ctor_get(v_t_4512_, 1);
v_size_4515_ = lean_ctor_get(v_t_4512_, 2);
v_shift_4516_ = lean_ctor_get_usize(v_t_4512_, 4);
v_tailOff_4517_ = lean_ctor_get(v_t_4512_, 3);
v_isSharedCheck_4528_ = !lean_is_exclusive(v_t_4512_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4519_ = v_t_4512_;
v_isShared_4520_ = v_isSharedCheck_4528_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_tailOff_4517_);
lean_inc(v_size_4515_);
lean_inc(v_tail_4514_);
lean_inc(v_root_4513_);
lean_dec(v_t_4512_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4528_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4521_; size_t v_sz_4522_; size_t v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4526_; 
lean_inc(v_fvarId_4510_);
v___x_4521_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__2(v_fvarId_4510_, v_e_4511_, v_root_4513_);
v_sz_4522_ = lean_array_size(v_tail_4514_);
v___x_4523_ = ((size_t)0ULL);
v___x_4524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1_spec__3(v_fvarId_4510_, v_e_4511_, v_sz_4522_, v___x_4523_, v_tail_4514_);
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 1, v___x_4524_);
lean_ctor_set(v___x_4519_, 0, v___x_4521_);
v___x_4526_ = v___x_4519_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4521_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v___x_4524_);
lean_ctor_set(v_reuseFailAlloc_4527_, 2, v_size_4515_);
lean_ctor_set(v_reuseFailAlloc_4527_, 3, v_tailOff_4517_);
lean_ctor_set_usize(v_reuseFailAlloc_4527_, 4, v_shift_4516_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1___boxed(lean_object* v_fvarId_4529_, lean_object* v_e_4530_, lean_object* v_t_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4529_, v_e_4530_, v_t_4531_);
lean_dec_ref(v_e_4530_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0(lean_object* v_f_4533_, lean_object* v_x_4534_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = lean_apply_1(v_f_4533_, v_x_4534_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_f_4536_, lean_object* v_as_4537_, lean_object* v_i_4538_, lean_object* v_acc_4539_){
_start:
{
lean_object* v___x_4540_; uint8_t v___x_4541_; 
v___x_4540_ = lean_array_get_size(v_as_4537_);
v___x_4541_ = lean_nat_dec_eq(v_i_4538_, v___x_4540_);
if (v___x_4541_ == 0)
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4542_ = lean_array_fget_borrowed(v_as_4537_, v_i_4538_);
lean_inc(v_f_4536_);
lean_inc(v___x_4542_);
v___x_4543_ = lean_apply_1(v_f_4536_, v___x_4542_);
v___x_4544_ = lean_unsigned_to_nat(1u);
v___x_4545_ = lean_nat_add(v_i_4538_, v___x_4544_);
lean_dec(v_i_4538_);
v___x_4546_ = lean_array_push(v_acc_4539_, v___x_4543_);
v_i_4538_ = v___x_4545_;
v_acc_4539_ = v___x_4546_;
goto _start;
}
else
{
lean_dec(v_i_4538_);
lean_dec(v_f_4536_);
return v_acc_4539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_f_4548_, lean_object* v_as_4549_, lean_object* v_i_4550_, lean_object* v_acc_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4548_, v_as_4549_, v_i_4550_, v_acc_4551_);
lean_dec_ref(v_as_4549_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_4553_, lean_object* v_as_4554_){
_start:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4555_ = lean_unsigned_to_nat(0u);
v___x_4556_ = lean_array_get_size(v_as_4554_);
v___x_4557_ = lean_mk_empty_array_with_capacity(v___x_4556_);
v___x_4558_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4553_, v_as_4554_, v___x_4555_, v___x_4557_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_4559_, lean_object* v_as_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4559_, v_as_4560_);
lean_dec_ref(v_as_4560_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_4562_, size_t v_sz_4563_, size_t v_i_4564_, lean_object* v_bs_4565_){
_start:
{
uint8_t v___x_4566_; 
v___x_4566_ = lean_usize_dec_lt(v_i_4564_, v_sz_4563_);
if (v___x_4566_ == 0)
{
lean_dec(v_f_4562_);
return v_bs_4565_;
}
else
{
lean_object* v_v_4567_; lean_object* v___x_4568_; lean_object* v_bs_x27_4569_; lean_object* v___y_4571_; 
v_v_4567_ = lean_array_uget(v_bs_4565_, v_i_4564_);
v___x_4568_ = lean_unsigned_to_nat(0u);
v_bs_x27_4569_ = lean_array_uset(v_bs_4565_, v_i_4564_, v___x_4568_);
switch(lean_obj_tag(v_v_4567_))
{
case 0:
{
lean_object* v_key_4576_; lean_object* v_val_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4585_; 
v_key_4576_ = lean_ctor_get(v_v_4567_, 0);
v_val_4577_ = lean_ctor_get(v_v_4567_, 1);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_v_4567_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4579_ = v_v_4567_;
v_isShared_4580_ = v_isSharedCheck_4585_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_val_4577_);
lean_inc(v_key_4576_);
lean_dec(v_v_4567_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4585_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4581_; lean_object* v___x_4583_; 
lean_inc(v_f_4562_);
v___x_4581_ = lean_apply_1(v_f_4562_, v_val_4577_);
if (v_isShared_4580_ == 0)
{
lean_ctor_set(v___x_4579_, 1, v___x_4581_);
v___x_4583_ = v___x_4579_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_key_4576_);
lean_ctor_set(v_reuseFailAlloc_4584_, 1, v___x_4581_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
v___y_4571_ = v___x_4583_;
goto v___jp_4570_;
}
}
}
case 1:
{
lean_object* v_node_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4594_; 
v_node_4586_ = lean_ctor_get(v_v_4567_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_v_4567_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4588_ = v_v_4567_;
v_isShared_4589_ = v_isSharedCheck_4594_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_node_4586_);
lean_dec(v_v_4567_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4594_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4590_; lean_object* v___x_4592_; 
lean_inc(v_f_4562_);
v___x_4590_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4562_, v_node_4586_);
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 0, v___x_4590_);
v___x_4592_ = v___x_4588_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4590_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
v___y_4571_ = v___x_4592_;
goto v___jp_4570_;
}
}
}
default: 
{
lean_object* v___x_4595_; 
v___x_4595_ = lean_box(2);
v___y_4571_ = v___x_4595_;
goto v___jp_4570_;
}
}
v___jp_4570_:
{
size_t v___x_4572_; size_t v___x_4573_; lean_object* v___x_4574_; 
v___x_4572_ = ((size_t)1ULL);
v___x_4573_ = lean_usize_add(v_i_4564_, v___x_4572_);
v___x_4574_ = lean_array_uset(v_bs_x27_4569_, v_i_4564_, v___y_4571_);
v_i_4564_ = v___x_4573_;
v_bs_4565_ = v___x_4574_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(lean_object* v_f_4596_, lean_object* v_n_4597_){
_start:
{
if (lean_obj_tag(v_n_4597_) == 0)
{
lean_object* v_es_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4608_; 
v_es_4598_ = lean_ctor_get(v_n_4597_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v_n_4597_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4600_ = v_n_4597_;
v_isShared_4601_ = v_isSharedCheck_4608_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_es_4598_);
lean_dec(v_n_4597_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4608_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
size_t v_sz_4602_; size_t v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4606_; 
v_sz_4602_ = lean_array_size(v_es_4598_);
v___x_4603_ = ((size_t)0ULL);
v___x_4604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4596_, v_sz_4602_, v___x_4603_, v_es_4598_);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v___x_4604_);
v___x_4606_ = v___x_4600_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4604_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
else
{
lean_object* v_ks_4609_; lean_object* v_vs_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4618_; 
v_ks_4609_ = lean_ctor_get(v_n_4597_, 0);
v_vs_4610_ = lean_ctor_get(v_n_4597_, 1);
v_isSharedCheck_4618_ = !lean_is_exclusive(v_n_4597_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4612_ = v_n_4597_;
v_isShared_4613_ = v_isSharedCheck_4618_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_vs_4610_);
lean_inc(v_ks_4609_);
lean_dec(v_n_4597_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4618_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v_val_4614_; lean_object* v___x_4616_; 
v_val_4614_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4596_, v_vs_4610_);
lean_dec_ref(v_vs_4610_);
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 1, v_val_4614_);
v___x_4616_ = v___x_4612_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_ks_4609_);
lean_ctor_set(v_reuseFailAlloc_4617_, 1, v_val_4614_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_4619_, lean_object* v_sz_4620_, lean_object* v_i_4621_, lean_object* v_bs_4622_){
_start:
{
size_t v_sz_boxed_4623_; size_t v_i_boxed_4624_; lean_object* v_res_4625_; 
v_sz_boxed_4623_ = lean_unbox_usize(v_sz_4620_);
lean_dec(v_sz_4620_);
v_i_boxed_4624_ = lean_unbox_usize(v_i_4621_);
lean_dec(v_i_4621_);
v_res_4625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4619_, v_sz_boxed_4623_, v_i_boxed_4624_, v_bs_4622_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(lean_object* v_pm_4626_, lean_object* v_f_4627_){
_start:
{
lean_object* v___f_4628_; lean_object* v___x_4629_; 
v___f_4628_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4628_, 0, v_f_4627_);
v___x_4629_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v___f_4628_, v_pm_4626_);
return v___x_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_replaceFVarId(lean_object* v_fvarId_4630_, lean_object* v_e_4631_, lean_object* v_lctx_4632_){
_start:
{
lean_object* v_lctx_4633_; lean_object* v_fvarIdToDecl_4634_; lean_object* v_decls_4635_; lean_object* v_auxDeclToFullName_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4646_; 
lean_inc(v_fvarId_4630_);
v_lctx_4633_ = lean_local_ctx_erase(v_lctx_4632_, v_fvarId_4630_);
v_fvarIdToDecl_4634_ = lean_ctor_get(v_lctx_4633_, 0);
v_decls_4635_ = lean_ctor_get(v_lctx_4633_, 1);
v_auxDeclToFullName_4636_ = lean_ctor_get(v_lctx_4633_, 2);
v_isSharedCheck_4646_ = !lean_is_exclusive(v_lctx_4633_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4638_ = v_lctx_4633_;
v_isShared_4639_ = v_isSharedCheck_4646_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_auxDeclToFullName_4636_);
lean_inc(v_decls_4635_);
lean_inc(v_fvarIdToDecl_4634_);
lean_dec(v_lctx_4633_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4646_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___f_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4644_; 
lean_inc_ref(v_e_4631_);
lean_inc(v_fvarId_4630_);
v___f_4640_ = lean_alloc_closure((void*)(l_Lean_LocalContext_replaceFVarId___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4640_, 0, v_fvarId_4630_);
lean_closure_set(v___f_4640_, 1, v_e_4631_);
v___x_4641_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_fvarIdToDecl_4634_, v___f_4640_);
v___x_4642_ = l_Lean_PersistentArray_mapM___at___00Lean_LocalContext_replaceFVarId_spec__1(v_fvarId_4630_, v_e_4631_, v_decls_4635_);
lean_dec_ref(v_e_4631_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 1, v___x_4642_);
lean_ctor_set(v___x_4638_, 0, v___x_4641_);
v___x_4644_ = v___x_4638_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v___x_4641_);
lean_ctor_set(v_reuseFailAlloc_4645_, 1, v___x_4642_);
lean_ctor_set(v_reuseFailAlloc_4645_, 2, v_auxDeclToFullName_4636_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0(lean_object* v_00_u03b2_4647_, lean_object* v_00_u03c3_4648_, lean_object* v_pm_4649_, lean_object* v_f_4650_){
_start:
{
lean_object* v___x_4651_; 
v___x_4651_ = l_Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0___redArg(v_pm_4649_, v_f_4650_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0___redArg(lean_object* v_pm_4652_, lean_object* v_f_4653_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4653_, v_pm_4652_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0(lean_object* v_00_u03b2_4655_, lean_object* v_00_u03c3_4656_, lean_object* v_pm_4657_, lean_object* v_f_4658_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4658_, v_pm_4657_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4660_, lean_object* v_00_u03b2_4661_, lean_object* v_00_u03c3_4662_, lean_object* v_f_4663_, lean_object* v_n_4664_){
_start:
{
lean_object* v___x_4665_; 
v___x_4665_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1___redArg(v_f_4663_, v_n_4664_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4666_, lean_object* v_00_u03b2_4667_, lean_object* v_00_u03c3_4668_, lean_object* v_f_4669_, size_t v_sz_4670_, size_t v_i_4671_, lean_object* v_bs_4672_){
_start:
{
lean_object* v___x_4673_; 
v___x_4673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___redArg(v_f_4669_, v_sz_4670_, v_i_4671_, v_bs_4672_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4674_, lean_object* v_00_u03b2_4675_, lean_object* v_00_u03c3_4676_, lean_object* v_f_4677_, lean_object* v_sz_4678_, lean_object* v_i_4679_, lean_object* v_bs_4680_){
_start:
{
size_t v_sz_boxed_4681_; size_t v_i_boxed_4682_; lean_object* v_res_4683_; 
v_sz_boxed_4681_ = lean_unbox_usize(v_sz_4678_);
lean_dec(v_sz_4678_);
v_i_boxed_4682_ = lean_unbox_usize(v_i_4679_);
lean_dec(v_i_4679_);
v_res_4683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4674_, v_00_u03b2_4675_, v_00_u03c3_4676_, v_f_4677_, v_sz_boxed_4681_, v_i_boxed_4682_, v_bs_4680_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_4684_, lean_object* v_00_u03b2_4685_, lean_object* v_f_4686_, lean_object* v_as_4687_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___redArg(v_f_4686_, v_as_4687_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_4689_, lean_object* v_00_u03b2_4690_, lean_object* v_f_4691_, lean_object* v_as_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4689_, v_00_u03b2_4690_, v_f_4691_, v_as_4692_);
lean_dec_ref(v_as_4692_);
return v_res_4693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b1_4694_, lean_object* v_00_u03b2_4695_, lean_object* v_f_4696_, lean_object* v_as_4697_, lean_object* v_i_4698_, lean_object* v_acc_4699_, lean_object* v_hle_4700_){
_start:
{
lean_object* v___x_4701_; 
v___x_4701_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_f_4696_, v_as_4697_, v_i_4698_, v_acc_4699_);
return v___x_4701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4702_, lean_object* v_00_u03b2_4703_, lean_object* v_f_4704_, lean_object* v_as_4705_, lean_object* v_i_4706_, lean_object* v_acc_4707_, lean_object* v_hle_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_LocalContext_replaceFVarId_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b1_4702_, v_00_u03b2_4703_, v_f_4704_, v_as_4705_, v_i_4706_, v_acc_4707_, v_hle_4708_);
lean_dec_ref(v_as_4705_);
return v_res_4709_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Control(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
