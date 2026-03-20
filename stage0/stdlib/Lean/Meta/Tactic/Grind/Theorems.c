// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Theorems
// Imports: public import Lean.HeadIndex public import Lean.Meta.Basic import Lean.Meta.Eqns import Init.Data.Range.Polymorphic.Iterators
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
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadEnvMetaM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_getConstVal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_decl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_decl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_fvar_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_stx_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_stx_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_local_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_local_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedOrigin_default = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedOrigin = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedOrigin_default___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.Grind.Origin.decl"};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__4;
static const lean_string_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.Grind.Origin.fvar"};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.Grind.Origin.stx"};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__8_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.Grind.Origin.local"};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__11_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprOrigin_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin_repr___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprOrigin_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instReprOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instReprOrigin_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instReprOrigin___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instReprOrigin = (const lean_object*)&l_Lean_Meta_Grind_instReprOrigin___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqOrigin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqOrigin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instBEqOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instBEqOrigin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instBEqOrigin___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instBEqOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instBEqOrigin = (const lean_object*)&l_Lean_Meta_Grind_instBEqOrigin___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableOrigin___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instHashableOrigin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instHashableOrigin___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instHashableOrigin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instHashableOrigin = (const lean_object*)&l_Lean_Meta_Grind_instHashableOrigin___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedTheorems___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedTheorems___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__8_value),((lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10;
static const lean_string_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Tactic.Grind.Theorems"};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Grind.Theorems.insert"};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15_value;
static const lean_closure_object l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_isErased___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_isErased(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "` is not marked with the `[grind]` attribute"};
static const lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getProofForDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "invalid `grind` theorem `"};
static const lean_object* l_Lean_Meta_Grind_getProofForDecl___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getProofForDecl___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_getProofForDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofForDecl___closed__1;
static const lean_string_object l_Lean_Meta_Grind_getProofForDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "`, type is not a proposition"};
static const lean_object* l_Lean_Meta_Grind_getProofForDecl___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getProofForDecl___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_getProofForDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofForDecl___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofForDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
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
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Meta_Grind_Origin_ctorIdx(v_x_6_);
lean_dec_ref(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
if (lean_obj_tag(v_t_8_) == 2)
{
lean_object* v_id_10_; lean_object* v_ref_11_; lean_object* v___x_12_; 
v_id_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_id_10_);
v_ref_11_ = lean_ctor_get(v_t_8_, 1);
lean_inc(v_ref_11_);
lean_dec_ref(v_t_8_);
v___x_12_ = lean_apply_2(v_k_9_, v_id_10_, v_ref_11_);
return v___x_12_;
}
else
{
lean_object* v_declName_13_; lean_object* v___x_14_; 
v_declName_13_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_declName_13_);
lean_dec_ref(v_t_8_);
v___x_14_ = lean_apply_1(v_k_9_, v_declName_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_Grind_Origin_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_decl_elim___redArg(lean_object* v_t_27_, lean_object* v_decl_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_27_, v_decl_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_decl_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_decl_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_31_, v_decl_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_fvar_elim___redArg(lean_object* v_t_35_, lean_object* v_fvar_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_35_, v_fvar_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_fvar_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_fvar_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_39_, v_fvar_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_stx_elim___redArg(lean_object* v_t_43_, lean_object* v_stx_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_43_, v_stx_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_stx_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_stx_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_47_, v_stx_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_local_elim___redArg(lean_object* v_t_51_, lean_object* v_local_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_51_, v_local_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_local_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_local_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Grind_Origin_ctorElim___redArg(v_t_55_, v_local_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(2u);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = lean_nat_to_int(v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprOrigin_repr(lean_object* v_x_91_, lean_object* v_prec_92_){
_start:
{
switch(lean_obj_tag(v_x_91_))
{
case 0:
{
lean_object* v_declName_93_; lean_object* v___y_95_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_declName_93_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_declName_93_);
lean_dec_ref(v_x_91_);
v___x_104_ = lean_unsigned_to_nat(1024u);
v___x_105_ = lean_nat_dec_le(v___x_104_, v_prec_92_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__3, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3);
v___y_95_ = v___x_106_;
goto v___jp_94_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__4, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4);
v___y_95_ = v___x_107_;
goto v___jp_94_;
}
v___jp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_96_ = ((lean_object*)(l_Lean_Meta_Grind_instReprOrigin_repr___closed__2));
v___x_97_ = lean_unsigned_to_nat(1024u);
v___x_98_ = l_Lean_Name_reprPrec(v_declName_93_, v___x_97_);
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_96_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_100_, 0, v___y_95_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = 0;
v___x_102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1, v___x_101_);
v___x_103_ = l_Repr_addAppParen(v___x_102_, v_prec_92_);
return v___x_103_;
}
}
case 1:
{
lean_object* v_fvarId_108_; lean_object* v___y_110_; lean_object* v___x_119_; uint8_t v___x_120_; 
v_fvarId_108_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_fvarId_108_);
lean_dec_ref(v_x_91_);
v___x_119_ = lean_unsigned_to_nat(1024u);
v___x_120_ = lean_nat_dec_le(v___x_119_, v_prec_92_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; 
v___x_121_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__3, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3);
v___y_110_ = v___x_121_;
goto v___jp_109_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__4, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4);
v___y_110_ = v___x_122_;
goto v___jp_109_;
}
v___jp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_111_ = ((lean_object*)(l_Lean_Meta_Grind_instReprOrigin_repr___closed__7));
v___x_112_ = lean_unsigned_to_nat(1024u);
v___x_113_ = l_Lean_Name_reprPrec(v_fvarId_108_, v___x_112_);
v___x_114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_111_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_115_, 0, v___y_110_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = 0;
v___x_117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_116_);
v___x_118_ = l_Repr_addAppParen(v___x_117_, v_prec_92_);
return v___x_118_;
}
}
case 2:
{
lean_object* v_id_123_; lean_object* v_ref_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_148_; 
v_id_123_ = lean_ctor_get(v_x_91_, 0);
v_ref_124_ = lean_ctor_get(v_x_91_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_91_);
if (v_isSharedCheck_148_ == 0)
{
v___x_126_ = v_x_91_;
v_isShared_127_ = v_isSharedCheck_148_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_ref_124_);
lean_inc(v_id_123_);
lean_dec(v_x_91_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_148_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___y_129_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1024u);
v___x_145_ = lean_nat_dec_le(v___x_144_, v_prec_92_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__3, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3);
v___y_129_ = v___x_146_;
goto v___jp_128_;
}
else
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__4, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4);
v___y_129_ = v___x_147_;
goto v___jp_128_;
}
v___jp_128_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_130_ = lean_box(1);
v___x_131_ = ((lean_object*)(l_Lean_Meta_Grind_instReprOrigin_repr___closed__10));
v___x_132_ = lean_unsigned_to_nat(1024u);
v___x_133_ = l_Lean_Name_reprPrec(v_id_123_, v___x_132_);
if (v_isShared_127_ == 0)
{
lean_ctor_set_tag(v___x_126_, 5);
lean_ctor_set(v___x_126_, 1, v___x_133_);
lean_ctor_set(v___x_126_, 0, v___x_131_);
v___x_135_ = v___x_126_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_143_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_130_);
v___x_137_ = l_Lean_Syntax_instRepr_repr(v_ref_124_, v___x_132_);
v___x_138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_139_, 0, v___y_129_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
v___x_140_ = 0;
v___x_141_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_141_, 0, v___x_139_);
lean_ctor_set_uint8(v___x_141_, sizeof(void*)*1, v___x_140_);
v___x_142_ = l_Repr_addAppParen(v___x_141_, v_prec_92_);
return v___x_142_;
}
}
}
}
default: 
{
lean_object* v_id_149_; lean_object* v___y_151_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_id_149_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_id_149_);
lean_dec_ref(v_x_91_);
v___x_160_ = lean_unsigned_to_nat(1024u);
v___x_161_ = lean_nat_dec_le(v___x_160_, v_prec_92_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__3, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__3_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__3);
v___y_151_ = v___x_162_;
goto v___jp_150_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Lean_Meta_Grind_instReprOrigin_repr___closed__4, &l_Lean_Meta_Grind_instReprOrigin_repr___closed__4_once, _init_l_Lean_Meta_Grind_instReprOrigin_repr___closed__4);
v___y_151_ = v___x_163_;
goto v___jp_150_;
}
v___jp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_152_ = ((lean_object*)(l_Lean_Meta_Grind_instReprOrigin_repr___closed__13));
v___x_153_ = lean_unsigned_to_nat(1024u);
v___x_154_ = l_Lean_Name_reprPrec(v_id_149_, v___x_153_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_152_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_156_, 0, v___y_151_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v___x_157_ = 0;
v___x_158_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_158_, 0, v___x_156_);
lean_ctor_set_uint8(v___x_158_, sizeof(void*)*1, v___x_157_);
v___x_159_ = l_Repr_addAppParen(v___x_158_, v_prec_92_);
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprOrigin_repr___boxed(lean_object* v_x_164_, lean_object* v_prec_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_Grind_instReprOrigin_repr(v_x_164_, v_prec_165_);
lean_dec(v_prec_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key(lean_object* v_x_169_){
_start:
{
lean_object* v_declName_170_; 
v_declName_170_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_declName_170_);
return v_declName_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key___boxed(lean_object* v_x_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Meta_Grind_Origin_key(v_x_171_);
lean_dec_ref(v_x_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp(lean_object* v_o_173_){
_start:
{
switch(lean_obj_tag(v_o_173_))
{
case 0:
{
lean_object* v_declName_174_; uint8_t v___x_175_; lean_object* v___x_176_; 
v_declName_174_ = lean_ctor_get(v_o_173_, 0);
lean_inc(v_declName_174_);
lean_dec_ref(v_o_173_);
v___x_175_ = 0;
v___x_176_ = l_Lean_MessageData_ofConstName(v_declName_174_, v___x_175_);
return v___x_176_;
}
case 1:
{
lean_object* v_fvarId_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_fvarId_177_ = lean_ctor_get(v_o_173_, 0);
lean_inc(v_fvarId_177_);
lean_dec_ref(v_o_173_);
v___x_178_ = l_Lean_mkFVar(v_fvarId_177_);
v___x_179_ = l_Lean_MessageData_ofExpr(v___x_178_);
return v___x_179_;
}
case 2:
{
lean_object* v_ref_180_; lean_object* v___x_181_; 
v_ref_180_ = lean_ctor_get(v_o_173_, 1);
lean_inc(v_ref_180_);
lean_dec_ref(v_o_173_);
v___x_181_ = l_Lean_MessageData_ofSyntax(v_ref_180_);
return v___x_181_;
}
default: 
{
lean_object* v_id_182_; lean_object* v___x_183_; 
v_id_182_ = lean_ctor_get(v_o_173_, 0);
lean_inc(v_id_182_);
lean_dec_ref(v_o_173_);
v___x_183_ = l_Lean_MessageData_ofName(v_id_182_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqOrigin___lam__0(lean_object* v_a_184_, lean_object* v_b_185_){
_start:
{
lean_object* v___y_187_; lean_object* v_declName_190_; 
v_declName_190_ = lean_ctor_get(v_a_184_, 0);
v___y_187_ = v_declName_190_;
goto v___jp_186_;
v___jp_186_:
{
lean_object* v_declName_188_; uint8_t v___x_189_; 
v_declName_188_ = lean_ctor_get(v_b_185_, 0);
v___x_189_ = lean_name_eq(v___y_187_, v_declName_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqOrigin___lam__0___boxed(lean_object* v_a_191_, lean_object* v_b_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Lean_Meta_Grind_instBEqOrigin___lam__0(v_a_191_, v_b_192_);
lean_dec_ref(v_b_192_);
lean_dec_ref(v_a_191_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0(void){
_start:
{
lean_object* v___x_197_; uint64_t v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(1723u);
v___x_198_ = lean_uint64_of_nat(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableOrigin___lam__0(lean_object* v_a_199_){
_start:
{
lean_object* v___y_201_; lean_object* v_declName_204_; 
v_declName_204_ = lean_ctor_get(v_a_199_, 0);
v___y_201_ = v_declName_204_;
goto v___jp_200_;
v___jp_200_:
{
if (lean_obj_tag(v___y_201_) == 0)
{
uint64_t v___x_202_; 
v___x_202_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0, &l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0);
return v___x_202_;
}
else
{
uint64_t v_hash_203_; 
v_hash_203_ = lean_ctor_get_uint64(v___y_201_, sizeof(void*)*2);
return v_hash_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed(lean_object* v_a_205_){
_start:
{
uint64_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Lean_Meta_Grind_instHashableOrigin___lam__0(v_a_205_);
lean_dec_ref(v_a_205_);
v_r_207_ = lean_box_uint64(v_res_206_);
return v_r_207_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_210_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__0);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0(lean_object* v_00_u03b2_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0___closed__1);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__0);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedTheorems_default_spec__0(lean_box(0));
return v___x_218_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__2);
v___x_220_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1);
v___x_221_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
lean_ctor_set(v___x_221_, 2, v___x_219_);
lean_ctor_set(v___x_221_, 3, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_object* v_a_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedTheorems___closed__0(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_box(0));
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems(lean_object* v_a_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems___closed__0);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems___closed__0, &l_Lean_Meta_Grind_instInhabitedTheorems___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems___closed__0);
v___x_247_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__9));
v___x_248_ = l_instInhabitedOfMonad___redArg(v___x_247_, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_252_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__13));
v___x_253_ = lean_unsigned_to_nat(6u);
v___x_254_ = lean_unsigned_to_nat(82u);
v___x_255_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__12));
v___x_256_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__11));
v___x_257_ = l_mkPanicMessageWithDecl(v___x_256_, v___x_255_, v___x_254_, v___x_253_, v___x_252_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___redArg(lean_object* v_inst_260_, lean_object* v_s_261_, lean_object* v_thm_262_){
_start:
{
lean_object* v_getSymbols_263_; lean_object* v_setSymbols_264_; lean_object* v_getOrigin_265_; lean_object* v___x_266_; lean_object* v___x_270_; 
v_getSymbols_263_ = lean_ctor_get(v_inst_260_, 0);
lean_inc_ref(v_getSymbols_263_);
v_setSymbols_264_ = lean_ctor_get(v_inst_260_, 1);
lean_inc(v_setSymbols_264_);
v_getOrigin_265_ = lean_ctor_get(v_inst_260_, 2);
lean_inc_ref(v_getOrigin_265_);
lean_dec_ref(v_inst_260_);
v___x_266_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10, &l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10_once, _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__10);
lean_inc(v_thm_262_);
v___x_270_ = lean_apply_1(v_getSymbols_263_, v_thm_262_);
if (lean_obj_tag(v___x_270_) == 1)
{
lean_object* v_head_271_; 
v_head_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_head_271_);
if (lean_obj_tag(v_head_271_) == 2)
{
lean_object* v_tail_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_320_; 
v_tail_272_ = lean_ctor_get(v___x_270_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_270_, 0);
lean_dec(v_unused_321_);
v___x_274_ = v___x_270_;
v_isShared_275_ = v_isSharedCheck_320_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_tail_272_);
lean_dec(v___x_270_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_320_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v_constName_276_; lean_object* v_smap_277_; lean_object* v_origins_278_; lean_object* v_erased_279_; lean_object* v_omap_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_319_; 
v_constName_276_ = lean_ctor_get(v_head_271_, 0);
lean_inc(v_constName_276_);
lean_dec_ref(v_head_271_);
v_smap_277_ = lean_ctor_get(v_s_261_, 0);
v_origins_278_ = lean_ctor_get(v_s_261_, 1);
v_erased_279_ = lean_ctor_get(v_s_261_, 2);
v_omap_280_ = lean_ctor_get(v_s_261_, 3);
v_isSharedCheck_319_ = !lean_is_exclusive(v_s_261_);
if (v_isSharedCheck_319_ == 0)
{
v___x_282_ = v_s_261_;
v_isShared_283_ = v_isSharedCheck_319_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_omap_280_);
lean_inc(v_erased_279_);
lean_inc(v_origins_278_);
lean_inc(v_smap_277_);
lean_dec(v_s_261_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_319_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___f_284_; lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_thm_288_; lean_object* v_origin_289_; lean_object* v___x_290_; lean_object* v_origins_291_; lean_object* v_erased_292_; lean_object* v___y_294_; lean_object* v___x_312_; 
v___f_284_ = ((lean_object*)(l_Lean_Meta_Grind_instBEqOrigin___closed__0));
v___f_285_ = ((lean_object*)(l_Lean_Meta_Grind_instHashableOrigin___closed__0));
v___x_286_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_287_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
v_thm_288_ = lean_apply_2(v_setSymbols_264_, v_thm_262_, v_tail_272_);
lean_inc(v_thm_288_);
v_origin_289_ = lean_apply_1(v_getOrigin_265_, v_thm_288_);
v___x_290_ = lean_box(0);
lean_inc_ref(v_origin_289_);
v_origins_291_ = l_Lean_PersistentHashMap_insert___redArg(v___f_284_, v___f_285_, v_origins_278_, v_origin_289_, v___x_290_);
lean_inc_ref(v_origin_289_);
v_erased_292_ = l_Lean_PersistentHashMap_erase___redArg(v___f_284_, v___f_285_, v_erased_279_, v_origin_289_);
lean_inc(v_constName_276_);
lean_inc_ref(v_smap_277_);
v___x_312_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_286_, v___x_287_, v_smap_277_, v_constName_276_);
if (lean_obj_tag(v___x_312_) == 1)
{
lean_object* v_val_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_val_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_313_);
lean_dec_ref(v___x_312_);
lean_inc(v_thm_288_);
v___x_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_314_, 0, v_thm_288_);
lean_ctor_set(v___x_314_, 1, v_val_313_);
v___x_315_ = l_Lean_PersistentHashMap_insert___redArg(v___x_286_, v___x_287_, v_smap_277_, v_constName_276_, v___x_314_);
v___y_294_ = v___x_315_;
goto v___jp_293_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v___x_312_);
v___x_316_ = lean_box(0);
lean_inc(v_thm_288_);
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v_thm_288_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_Lean_PersistentHashMap_insert___redArg(v___x_286_, v___x_287_, v_smap_277_, v_constName_276_, v___x_317_);
v___y_294_ = v___x_318_;
goto v___jp_293_;
}
v___jp_293_:
{
lean_object* v___x_295_; 
lean_inc_ref(v_origin_289_);
lean_inc_ref(v_omap_280_);
v___x_295_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_284_, v___f_285_, v_omap_280_, v_origin_289_);
if (lean_obj_tag(v___x_295_) == 1)
{
lean_object* v_val_296_; lean_object* v___x_298_; 
v_val_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_val_296_);
lean_dec_ref(v___x_295_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 1, v_val_296_);
lean_ctor_set(v___x_274_, 0, v_thm_288_);
v___x_298_ = v___x_274_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_thm_288_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_val_296_);
v___x_298_ = v_reuseFailAlloc_303_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_PersistentHashMap_insert___redArg(v___f_284_, v___f_285_, v_omap_280_, v_origin_289_, v___x_298_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 3, v___x_299_);
lean_ctor_set(v___x_282_, 2, v_erased_292_);
lean_ctor_set(v___x_282_, 1, v_origins_291_);
lean_ctor_set(v___x_282_, 0, v___y_294_);
v___x_301_ = v___x_282_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___y_294_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_origins_291_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_erased_292_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_306_; 
lean_dec(v___x_295_);
v___x_304_ = lean_box(0);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 1, v___x_304_);
lean_ctor_set(v___x_274_, 0, v_thm_288_);
v___x_306_ = v___x_274_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_thm_288_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_311_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_307_ = l_Lean_PersistentHashMap_insert___redArg(v___f_284_, v___f_285_, v_omap_280_, v_origin_289_, v___x_306_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 3, v___x_307_);
lean_ctor_set(v___x_282_, 2, v_erased_292_);
lean_ctor_set(v___x_282_, 1, v_origins_291_);
lean_ctor_set(v___x_282_, 0, v___y_294_);
v___x_309_ = v___x_282_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___y_294_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_origins_291_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v_erased_292_);
lean_ctor_set(v_reuseFailAlloc_310_, 3, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_270_);
lean_dec(v_head_271_);
lean_dec_ref(v_getOrigin_265_);
lean_dec(v_setSymbols_264_);
lean_dec(v_thm_262_);
lean_dec_ref(v_s_261_);
goto v___jp_267_;
}
}
else
{
lean_dec(v___x_270_);
lean_dec_ref(v_getOrigin_265_);
lean_dec(v_setSymbols_264_);
lean_dec(v_thm_262_);
lean_dec_ref(v_s_261_);
goto v___jp_267_;
}
v___jp_267_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14, &l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14_once, _init_l_Lean_Meta_Grind_Theorems_insert___redArg___closed__14);
v___x_269_ = l_panic___redArg(v___x_266_, v___x_268_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert(lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_s_324_, lean_object* v_thm_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_323_, v_s_324_, v_thm_325_);
return v___x_326_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_327_, lean_object* v_i_328_, lean_object* v_k_329_){
_start:
{
lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_array_get_size(v_keys_327_);
v___x_338_ = lean_nat_dec_lt(v_i_328_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec(v_i_328_);
return v___x_338_;
}
else
{
lean_object* v_k_x27_339_; lean_object* v___y_341_; lean_object* v_declName_343_; 
v_k_x27_339_ = lean_array_fget_borrowed(v_keys_327_, v_i_328_);
v_declName_343_ = lean_ctor_get(v_k_329_, 0);
v___y_341_ = v_declName_343_;
goto v___jp_340_;
v___jp_340_:
{
lean_object* v_declName_342_; 
v_declName_342_ = lean_ctor_get(v_k_x27_339_, 0);
lean_inc(v_declName_342_);
v___y_331_ = v___y_341_;
v___y_332_ = v_declName_342_;
goto v___jp_330_;
}
}
v___jp_330_:
{
uint8_t v___x_333_; 
v___x_333_ = lean_name_eq(v___y_331_, v___y_332_);
lean_dec(v___y_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_add(v_i_328_, v___x_334_);
lean_dec(v_i_328_);
v_i_328_ = v___x_335_;
goto _start;
}
else
{
lean_dec(v_i_328_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_344_, lean_object* v_i_345_, lean_object* v_k_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_keys_344_, v_i_345_, v_k_346_);
lean_dec_ref(v_k_346_);
lean_dec_ref(v_keys_344_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_349_; size_t v___x_350_; size_t v___x_351_; 
v___x_349_ = ((size_t)5ULL);
v___x_350_ = ((size_t)1ULL);
v___x_351_ = lean_usize_shift_left(v___x_350_, v___x_349_);
return v___x_351_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; 
v___x_352_ = ((size_t)1ULL);
v___x_353_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__0);
v___x_354_ = lean_usize_sub(v___x_353_, v___x_352_);
return v___x_354_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(lean_object* v_x_355_, size_t v_x_356_, lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
lean_object* v_es_358_; lean_object* v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v_j_363_; lean_object* v___x_364_; 
v_es_358_ = lean_ctor_get(v_x_355_, 0);
lean_inc_ref(v_es_358_);
lean_dec_ref(v_x_355_);
v___x_359_ = lean_box(2);
v___x_360_ = ((size_t)5ULL);
v___x_361_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1);
v___x_362_ = lean_usize_land(v_x_356_, v___x_361_);
v_j_363_ = lean_usize_to_nat(v___x_362_);
v___x_364_ = lean_array_get(v___x_359_, v_es_358_, v_j_363_);
lean_dec(v_j_363_);
lean_dec_ref(v_es_358_);
switch(lean_obj_tag(v___x_364_))
{
case 0:
{
lean_object* v_key_365_; lean_object* v___y_367_; lean_object* v_declName_370_; 
v_key_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_key_365_);
lean_dec_ref(v___x_364_);
v_declName_370_ = lean_ctor_get(v_x_357_, 0);
v___y_367_ = v_declName_370_;
goto v___jp_366_;
v___jp_366_:
{
lean_object* v_declName_368_; uint8_t v___x_369_; 
v_declName_368_ = lean_ctor_get(v_key_365_, 0);
lean_inc(v_declName_368_);
lean_dec(v_key_365_);
v___x_369_ = lean_name_eq(v___y_367_, v_declName_368_);
lean_dec(v_declName_368_);
return v___x_369_;
}
}
case 1:
{
lean_object* v_node_371_; size_t v___x_372_; 
v_node_371_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_node_371_);
lean_dec_ref(v___x_364_);
v___x_372_ = lean_usize_shift_right(v_x_356_, v___x_360_);
v_x_355_ = v_node_371_;
v_x_356_ = v___x_372_;
goto _start;
}
default: 
{
uint8_t v___x_374_; 
v___x_374_ = 0;
return v___x_374_;
}
}
}
else
{
lean_object* v_ks_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_ks_375_ = lean_ctor_get(v_x_355_, 0);
lean_inc_ref(v_ks_375_);
lean_dec_ref(v_x_355_);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_ks_375_, v___x_376_, v_x_357_);
lean_dec_ref(v_ks_375_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
size_t v_x_220__boxed_381_; uint8_t v_res_382_; lean_object* v_r_383_; 
v_x_220__boxed_381_ = lean_unbox_usize(v_x_379_);
lean_dec(v_x_379_);
v_res_382_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_378_, v_x_220__boxed_381_, v_x_380_);
lean_dec_ref(v_x_380_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
uint64_t v___y_387_; lean_object* v___y_391_; lean_object* v_declName_394_; 
v_declName_394_ = lean_ctor_get(v_x_385_, 0);
v___y_391_ = v_declName_394_;
goto v___jp_390_;
v___jp_386_:
{
size_t v___x_388_; uint8_t v___x_389_; 
v___x_388_ = lean_uint64_to_usize(v___y_387_);
v___x_389_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_384_, v___x_388_, v_x_385_);
return v___x_389_;
}
v___jp_390_:
{
if (lean_obj_tag(v___y_391_) == 0)
{
uint64_t v___x_392_; 
v___x_392_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0, &l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0);
v___y_387_ = v___x_392_;
goto v___jp_386_;
}
else
{
uint64_t v_hash_393_; 
v_hash_393_ = lean_ctor_get_uint64(v___y_391_, sizeof(void*)*2);
v___y_387_ = v_hash_393_;
goto v___jp_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg___boxed(lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_x_395_, v_x_396_);
lean_dec_ref(v_x_396_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object* v_s_399_, lean_object* v_origin_400_){
_start:
{
lean_object* v_origins_401_; uint8_t v___x_402_; 
v_origins_401_ = lean_ctor_get(v_s_399_, 1);
lean_inc_ref(v_origins_401_);
lean_dec_ref(v_s_399_);
v___x_402_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_origins_401_, v_origin_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___redArg___boxed(lean_object* v_s_403_, lean_object* v_origin_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_403_, v_origin_404_);
lean_dec_ref(v_origin_404_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_contains(lean_object* v_00_u03b1_407_, lean_object* v_s_408_, lean_object* v_origin_409_){
_start:
{
uint8_t v___x_410_; 
v___x_410_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_408_, v_origin_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___boxed(lean_object* v_00_u03b1_411_, lean_object* v_s_412_, lean_object* v_origin_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Lean_Meta_Grind_Theorems_contains(v_00_u03b1_411_, v_s_412_, v_origin_413_);
lean_dec_ref(v_origin_413_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(lean_object* v_00_u03b2_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
uint8_t v___x_419_; 
v___x_419_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_x_417_, v_x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___boxed(lean_object* v_00_u03b2_420_, lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(v_00_u03b2_420_, v_x_421_, v_x_422_);
lean_dec_ref(v_x_422_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(lean_object* v_00_u03b2_425_, lean_object* v_x_426_, size_t v_x_427_, lean_object* v_x_428_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_426_, v_x_427_, v_x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
size_t v_x_327__boxed_434_; uint8_t v_res_435_; lean_object* v_r_436_; 
v_x_327__boxed_434_ = lean_unbox_usize(v_x_432_);
lean_dec(v_x_432_);
v_res_435_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(v_00_u03b2_430_, v_x_431_, v_x_327__boxed_434_, v_x_433_);
lean_dec_ref(v_x_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_437_, lean_object* v_keys_438_, lean_object* v_vals_439_, lean_object* v_heq_440_, lean_object* v_i_441_, lean_object* v_k_442_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_keys_438_, v_i_441_, v_k_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_444_, lean_object* v_keys_445_, lean_object* v_vals_446_, lean_object* v_heq_447_, lean_object* v_i_448_, lean_object* v_k_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(v_00_u03b2_444_, v_keys_445_, v_vals_446_, v_heq_447_, v_i_448_, v_k_449_);
lean_dec_ref(v_k_449_);
lean_dec_ref(v_vals_446_);
lean_dec_ref(v_keys_445_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_452_, lean_object* v_v_453_, lean_object* v_i_454_){
_start:
{
lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_464_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_array_get_size(v_xs_452_);
v___x_467_ = lean_nat_dec_lt(v_i_454_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec(v_i_454_);
v___x_468_ = lean_box(0);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v_declName_470_; 
v___x_469_ = lean_array_fget_borrowed(v_xs_452_, v_i_454_);
v_declName_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_declName_470_);
v___y_464_ = v_declName_470_;
goto v___jp_463_;
}
v___jp_455_:
{
uint8_t v___x_458_; 
v___x_458_ = lean_name_eq(v___y_456_, v___y_457_);
lean_dec(v___y_456_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_add(v_i_454_, v___x_459_);
lean_dec(v_i_454_);
v_i_454_ = v___x_460_;
goto _start;
}
else
{
lean_object* v___x_462_; 
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v_i_454_);
return v___x_462_;
}
}
v___jp_463_:
{
lean_object* v_declName_465_; 
v_declName_465_ = lean_ctor_get(v_v_453_, 0);
v___y_456_ = v___y_464_;
v___y_457_ = v_declName_465_;
goto v___jp_455_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_471_, lean_object* v_v_472_, lean_object* v_i_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(v_xs_471_, v_v_472_, v_i_473_);
lean_dec_ref(v_v_472_);
lean_dec_ref(v_xs_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(lean_object* v_xs_475_, lean_object* v_v_476_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(v_xs_475_, v_v_476_, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_479_, lean_object* v_v_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(v_xs_479_, v_v_480_);
lean_dec_ref(v_v_480_);
lean_dec_ref(v_xs_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(lean_object* v_x_482_, size_t v_x_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v_es_485_; lean_object* v___x_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; lean_object* v_j_490_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v_entry_504_; 
v_es_485_ = lean_ctor_get(v_x_482_, 0);
v___x_486_ = lean_box(2);
v___x_487_ = ((size_t)5ULL);
v___x_488_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1);
v___x_489_ = lean_usize_land(v_x_483_, v___x_488_);
v_j_490_ = lean_usize_to_nat(v___x_489_);
v_entry_504_ = lean_array_get(v___x_486_, v_es_485_, v_j_490_);
switch(lean_obj_tag(v_entry_504_))
{
case 0:
{
lean_object* v_key_505_; lean_object* v___y_507_; lean_object* v_declName_509_; 
v_key_505_ = lean_ctor_get(v_entry_504_, 0);
lean_inc(v_key_505_);
lean_dec_ref(v_entry_504_);
v_declName_509_ = lean_ctor_get(v_x_484_, 0);
v___y_507_ = v_declName_509_;
goto v___jp_506_;
v___jp_506_:
{
lean_object* v_declName_508_; 
v_declName_508_ = lean_ctor_get(v_key_505_, 0);
lean_inc(v_declName_508_);
lean_dec(v_key_505_);
v___y_492_ = v___y_507_;
v___y_493_ = v_declName_508_;
goto v___jp_491_;
}
}
case 1:
{
lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_543_; 
lean_inc_ref(v_es_485_);
v_isSharedCheck_543_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v_x_482_, 0);
lean_dec(v_unused_544_);
v___x_511_ = v_x_482_;
v_isShared_512_ = v_isSharedCheck_543_;
goto v_resetjp_510_;
}
else
{
lean_dec(v_x_482_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_543_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_node_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_542_; 
v_node_513_ = lean_ctor_get(v_entry_504_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v_entry_504_);
if (v_isSharedCheck_542_ == 0)
{
v___x_515_ = v_entry_504_;
v_isShared_516_ = v_isSharedCheck_542_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_node_513_);
lean_dec(v_entry_504_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_542_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_entries_517_; size_t v___x_518_; lean_object* v_newNode_519_; lean_object* v___x_520_; 
v_entries_517_ = lean_array_set(v_es_485_, v_j_490_, v___x_486_);
v___x_518_ = lean_usize_shift_right(v_x_483_, v___x_487_);
v_newNode_519_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_node_513_, v___x_518_, v_x_484_);
lean_inc_ref(v_newNode_519_);
v___x_520_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v___x_522_; 
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v_newNode_519_);
v___x_522_ = v___x_515_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_newNode_519_);
v___x_522_ = v_reuseFailAlloc_527_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_array_set(v_entries_517_, v_j_490_, v___x_522_);
lean_dec(v_j_490_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_523_);
v___x_525_ = v___x_511_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_val_528_; lean_object* v_fst_529_; lean_object* v_snd_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_newNode_519_);
lean_del_object(v___x_515_);
v_val_528_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_val_528_);
lean_dec_ref(v___x_520_);
v_fst_529_ = lean_ctor_get(v_val_528_, 0);
v_snd_530_ = lean_ctor_get(v_val_528_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_val_528_);
if (v_isSharedCheck_541_ == 0)
{
v___x_532_ = v_val_528_;
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_snd_530_);
lean_inc(v_fst_529_);
lean_dec(v_val_528_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_fst_529_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_snd_530_);
v___x_535_ = v_reuseFailAlloc_540_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = lean_array_set(v_entries_517_, v_j_490_, v___x_535_);
lean_dec(v_j_490_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_536_);
v___x_538_ = v___x_511_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_490_);
return v_x_482_;
}
}
v___jp_491_:
{
uint8_t v___x_494_; 
v___x_494_ = lean_name_eq(v___y_492_, v___y_493_);
lean_dec(v___y_493_);
if (v___x_494_ == 0)
{
lean_dec(v_j_490_);
return v_x_482_;
}
else
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_502_; 
lean_inc_ref(v_es_485_);
v_isSharedCheck_502_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v_x_482_, 0);
lean_dec(v_unused_503_);
v___x_496_ = v_x_482_;
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_x_482_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = lean_array_set(v_es_485_, v_j_490_, v___x_486_);
lean_dec(v_j_490_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
else
{
lean_object* v_ks_545_; lean_object* v_vs_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_560_; 
v_ks_545_ = lean_ctor_get(v_x_482_, 0);
v_vs_546_ = lean_ctor_get(v_x_482_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_560_ == 0)
{
v___x_548_ = v_x_482_;
v_isShared_549_ = v_isSharedCheck_560_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_vs_546_);
lean_inc(v_ks_545_);
lean_dec(v_x_482_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_560_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; 
v___x_550_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(v_ks_545_, v_x_484_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v___x_552_; 
if (v_isShared_549_ == 0)
{
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_ks_545_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_vs_546_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v_val_554_; lean_object* v_keys_x27_555_; lean_object* v_vals_x27_556_; lean_object* v___x_558_; 
v_val_554_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_val_554_);
lean_dec_ref(v___x_550_);
lean_inc(v_val_554_);
v_keys_x27_555_ = l_Array_eraseIdx___redArg(v_ks_545_, v_val_554_);
v_vals_x27_556_ = l_Array_eraseIdx___redArg(v_vs_546_, v_val_554_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v_vals_x27_556_);
lean_ctor_set(v___x_548_, 0, v_keys_x27_555_);
v___x_558_ = v___x_548_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_keys_x27_555_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_vals_x27_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
size_t v_x_606__boxed_564_; lean_object* v_res_565_; 
v_x_606__boxed_564_ = lean_unbox_usize(v_x_562_);
lean_dec(v_x_562_);
v_res_565_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_561_, v_x_606__boxed_564_, v_x_563_);
lean_dec_ref(v_x_563_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
uint64_t v___y_569_; lean_object* v___y_573_; lean_object* v_declName_576_; 
v_declName_576_ = lean_ctor_get(v_x_567_, 0);
v___y_573_ = v_declName_576_;
goto v___jp_572_;
v___jp_568_:
{
size_t v_h_570_; lean_object* v___x_571_; 
v_h_570_ = lean_uint64_to_usize(v___y_569_);
v___x_571_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_566_, v_h_570_, v_x_567_);
return v___x_571_;
}
v___jp_572_:
{
if (lean_obj_tag(v___y_573_) == 0)
{
uint64_t v___x_574_; 
v___x_574_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0, &l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0);
v___y_569_ = v___x_574_;
goto v___jp_568_;
}
else
{
uint64_t v_hash_575_; 
v_hash_575_ = lean_ctor_get_uint64(v___y_573_, sizeof(void*)*2);
v___y_569_ = v_hash_575_;
goto v___jp_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg___boxed(lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_x_577_, v_x_578_);
lean_dec_ref(v_x_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
lean_object* v_ks_584_; lean_object* v_vs_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_614_; 
v_ks_584_ = lean_ctor_get(v_x_580_, 0);
v_vs_585_ = lean_ctor_get(v_x_580_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_614_ == 0)
{
v___x_587_ = v_x_580_;
v_isShared_588_ = v_isSharedCheck_614_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_vs_585_);
lean_inc(v_ks_584_);
lean_dec(v_x_580_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_614_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_array_get_size(v_ks_584_);
v___x_605_ = lean_nat_dec_lt(v_x_581_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_del_object(v___x_587_);
lean_dec(v_x_581_);
v___x_606_ = lean_array_push(v_ks_584_, v_x_582_);
v___x_607_ = lean_array_push(v_vs_585_, v_x_583_);
v___x_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
return v___x_608_;
}
else
{
lean_object* v_k_x27_609_; lean_object* v___y_611_; lean_object* v_declName_613_; 
v_k_x27_609_ = lean_array_fget_borrowed(v_ks_584_, v_x_581_);
v_declName_613_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_declName_613_);
v___y_611_ = v_declName_613_;
goto v___jp_610_;
v___jp_610_:
{
lean_object* v_declName_612_; 
v_declName_612_ = lean_ctor_get(v_k_x27_609_, 0);
lean_inc(v_declName_612_);
v___y_590_ = v___y_611_;
v___y_591_ = v_declName_612_;
goto v___jp_589_;
}
}
v___jp_589_:
{
uint8_t v___x_592_; 
v___x_592_ = lean_name_eq(v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec(v___y_590_);
if (v___x_592_ == 0)
{
lean_object* v___x_594_; 
if (v_isShared_588_ == 0)
{
v___x_594_ = v___x_587_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_ks_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_vs_585_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_nat_add(v_x_581_, v___x_595_);
lean_dec(v_x_581_);
v_x_580_ = v___x_594_;
v_x_581_ = v___x_596_;
goto _start;
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_599_ = lean_array_fset(v_ks_584_, v_x_581_, v_x_582_);
v___x_600_ = lean_array_fset(v_vs_585_, v_x_581_, v_x_583_);
lean_dec(v_x_581_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_600_);
lean_ctor_set(v___x_587_, 0, v___x_599_);
v___x_602_ = v___x_587_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(lean_object* v_n_615_, lean_object* v_k_616_, lean_object* v_v_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(v_n_615_, v___x_618_, v_k_616_, v_v_617_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(lean_object* v_x_621_, size_t v_x_622_, size_t v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
lean_object* v_es_626_; size_t v___x_627_; size_t v___x_628_; size_t v___x_629_; size_t v___x_630_; lean_object* v_j_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_es_626_ = lean_ctor_get(v_x_621_, 0);
v___x_627_ = ((size_t)5ULL);
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1);
v___x_630_ = lean_usize_land(v_x_622_, v___x_629_);
v_j_631_ = lean_usize_to_nat(v___x_630_);
v___x_632_ = lean_array_get_size(v_es_626_);
v___x_633_ = lean_nat_dec_lt(v_j_631_, v___x_632_);
if (v___x_633_ == 0)
{
lean_dec(v_j_631_);
lean_dec(v_x_625_);
lean_dec_ref(v_x_624_);
return v_x_621_;
}
else
{
lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_677_; 
lean_inc_ref(v_es_626_);
v_isSharedCheck_677_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; 
v_unused_678_ = lean_ctor_get(v_x_621_, 0);
lean_dec(v_unused_678_);
v___x_635_ = v_x_621_;
v_isShared_636_ = v_isSharedCheck_677_;
goto v_resetjp_634_;
}
else
{
lean_dec(v_x_621_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_677_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_v_637_; lean_object* v___x_638_; lean_object* v_xs_x27_639_; lean_object* v___y_641_; 
v_v_637_ = lean_array_fget(v_es_626_, v_j_631_);
v___x_638_ = lean_box(0);
v_xs_x27_639_ = lean_array_fset(v_es_626_, v_j_631_, v___x_638_);
switch(lean_obj_tag(v_v_637_))
{
case 0:
{
lean_object* v_key_646_; lean_object* v_val_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_664_; 
v_key_646_ = lean_ctor_get(v_v_637_, 0);
v_val_647_ = lean_ctor_get(v_v_637_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_v_637_);
if (v_isSharedCheck_664_ == 0)
{
v___x_649_ = v_v_637_;
v_isShared_650_ = v_isSharedCheck_664_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_val_647_);
lean_inc(v_key_646_);
lean_dec(v_v_637_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_664_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_661_; lean_object* v_declName_663_; 
v_declName_663_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_declName_663_);
v___y_661_ = v_declName_663_;
goto v___jp_660_;
v___jp_651_:
{
uint8_t v___x_654_; 
v___x_654_ = lean_name_eq(v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec(v___y_652_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; 
lean_del_object(v___x_649_);
v___x_655_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_646_, v_val_647_, v_x_624_, v_x_625_);
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
v___y_641_ = v___x_656_;
goto v___jp_640_;
}
else
{
lean_object* v___x_658_; 
lean_dec(v_val_647_);
lean_dec(v_key_646_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v_x_625_);
lean_ctor_set(v___x_649_, 0, v_x_624_);
v___x_658_ = v___x_649_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_x_624_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_x_625_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
v___y_641_ = v___x_658_;
goto v___jp_640_;
}
}
}
v___jp_660_:
{
lean_object* v_declName_662_; 
v_declName_662_ = lean_ctor_get(v_key_646_, 0);
lean_inc(v_declName_662_);
v___y_652_ = v___y_661_;
v___y_653_ = v_declName_662_;
goto v___jp_651_;
}
}
}
case 1:
{
lean_object* v_node_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_675_; 
v_node_665_ = lean_ctor_get(v_v_637_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v_v_637_);
if (v_isSharedCheck_675_ == 0)
{
v___x_667_ = v_v_637_;
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_node_665_);
lean_dec(v_v_637_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_669_ = lean_usize_shift_right(v_x_622_, v___x_627_);
v___x_670_ = lean_usize_add(v_x_623_, v___x_628_);
v___x_671_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_node_665_, v___x_669_, v___x_670_, v_x_624_, v_x_625_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_671_);
v___x_673_ = v___x_667_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
v___y_641_ = v___x_673_;
goto v___jp_640_;
}
}
}
default: 
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_x_624_);
lean_ctor_set(v___x_676_, 1, v_x_625_);
v___y_641_ = v___x_676_;
goto v___jp_640_;
}
}
v___jp_640_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = lean_array_fset(v_xs_x27_639_, v_j_631_, v___y_641_);
lean_dec(v_j_631_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_642_);
v___x_644_ = v___x_635_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
else
{
lean_object* v_ks_679_; lean_object* v_vs_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_700_; 
v_ks_679_ = lean_ctor_get(v_x_621_, 0);
v_vs_680_ = lean_ctor_get(v_x_621_, 1);
v_isSharedCheck_700_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_700_ == 0)
{
v___x_682_ = v_x_621_;
v_isShared_683_ = v_isSharedCheck_700_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_vs_680_);
lean_inc(v_ks_679_);
lean_dec(v_x_621_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_700_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_ks_679_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_vs_680_);
v___x_685_ = v_reuseFailAlloc_699_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v_newNode_686_; uint8_t v___y_688_; size_t v___x_694_; uint8_t v___x_695_; 
v_newNode_686_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(v___x_685_, v_x_624_, v_x_625_);
v___x_694_ = ((size_t)7ULL);
v___x_695_ = lean_usize_dec_le(v___x_694_, v_x_623_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_696_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_686_);
v___x_697_ = lean_unsigned_to_nat(4u);
v___x_698_ = lean_nat_dec_lt(v___x_696_, v___x_697_);
lean_dec(v___x_696_);
v___y_688_ = v___x_698_;
goto v___jp_687_;
}
else
{
v___y_688_ = v___x_695_;
goto v___jp_687_;
}
v___jp_687_:
{
if (v___y_688_ == 0)
{
lean_object* v_ks_689_; lean_object* v_vs_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_ks_689_ = lean_ctor_get(v_newNode_686_, 0);
lean_inc_ref(v_ks_689_);
v_vs_690_ = lean_ctor_get(v_newNode_686_, 1);
lean_inc_ref(v_vs_690_);
lean_dec_ref(v_newNode_686_);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0);
v___x_693_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_x_623_, v_ks_689_, v_vs_690_, v___x_691_, v___x_692_);
lean_dec_ref(v_vs_690_);
lean_dec_ref(v_ks_689_);
return v___x_693_;
}
else
{
return v_newNode_686_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(size_t v_depth_701_, lean_object* v_keys_702_, lean_object* v_vals_703_, lean_object* v_i_704_, lean_object* v_entries_705_){
_start:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_array_get_size(v_keys_702_);
v___x_707_ = lean_nat_dec_lt(v_i_704_, v___x_706_);
if (v___x_707_ == 0)
{
lean_dec(v_i_704_);
return v_entries_705_;
}
else
{
lean_object* v_k_708_; lean_object* v_v_709_; uint64_t v___y_711_; lean_object* v___y_723_; lean_object* v_declName_726_; 
v_k_708_ = lean_array_fget_borrowed(v_keys_702_, v_i_704_);
v_v_709_ = lean_array_fget_borrowed(v_vals_703_, v_i_704_);
v_declName_726_ = lean_ctor_get(v_k_708_, 0);
lean_inc(v_declName_726_);
v___y_723_ = v_declName_726_;
goto v___jp_722_;
v___jp_710_:
{
size_t v_h_712_; size_t v___x_713_; lean_object* v___x_714_; size_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v_h_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_h_712_ = lean_uint64_to_usize(v___y_711_);
v___x_713_ = ((size_t)5ULL);
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_715_ = ((size_t)1ULL);
v___x_716_ = lean_usize_sub(v_depth_701_, v___x_715_);
v___x_717_ = lean_usize_mul(v___x_713_, v___x_716_);
v_h_718_ = lean_usize_shift_right(v_h_712_, v___x_717_);
v___x_719_ = lean_nat_add(v_i_704_, v___x_714_);
lean_dec(v_i_704_);
lean_inc(v_v_709_);
lean_inc(v_k_708_);
v___x_720_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_entries_705_, v_h_718_, v_depth_701_, v_k_708_, v_v_709_);
v_i_704_ = v___x_719_;
v_entries_705_ = v___x_720_;
goto _start;
}
v___jp_722_:
{
if (lean_obj_tag(v___y_723_) == 0)
{
uint64_t v___x_724_; 
v___x_724_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0, &l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0);
v___y_711_ = v___x_724_;
goto v___jp_710_;
}
else
{
uint64_t v_hash_725_; 
v_hash_725_ = lean_ctor_get_uint64(v___y_723_, sizeof(void*)*2);
lean_dec(v___y_723_);
v___y_711_ = v_hash_725_;
goto v___jp_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_727_, lean_object* v_keys_728_, lean_object* v_vals_729_, lean_object* v_i_730_, lean_object* v_entries_731_){
_start:
{
size_t v_depth_boxed_732_; lean_object* v_res_733_; 
v_depth_boxed_732_ = lean_unbox_usize(v_depth_727_);
lean_dec(v_depth_727_);
v_res_733_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_depth_boxed_732_, v_keys_728_, v_vals_729_, v_i_730_, v_entries_731_);
lean_dec_ref(v_vals_729_);
lean_dec_ref(v_keys_728_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___boxed(lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
size_t v_x_905__boxed_739_; size_t v_x_906__boxed_740_; lean_object* v_res_741_; 
v_x_905__boxed_739_ = lean_unbox_usize(v_x_735_);
lean_dec(v_x_735_);
v_x_906__boxed_740_ = lean_unbox_usize(v_x_736_);
lean_dec(v_x_736_);
v_res_741_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_734_, v_x_905__boxed_739_, v_x_906__boxed_740_, v_x_737_, v_x_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
uint64_t v___y_746_; lean_object* v___y_751_; lean_object* v_declName_754_; 
v_declName_754_ = lean_ctor_get(v_x_743_, 0);
lean_inc(v_declName_754_);
v___y_751_ = v_declName_754_;
goto v___jp_750_;
v___jp_745_:
{
size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_uint64_to_usize(v___y_746_);
v___x_748_ = ((size_t)1ULL);
v___x_749_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_742_, v___x_747_, v___x_748_, v_x_743_, v_x_744_);
return v___x_749_;
}
v___jp_750_:
{
if (lean_obj_tag(v___y_751_) == 0)
{
uint64_t v___x_752_; 
v___x_752_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0, &l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0);
v___y_746_ = v___x_752_;
goto v___jp_745_;
}
else
{
uint64_t v_hash_753_; 
v_hash_753_ = lean_ctor_get_uint64(v___y_751_, sizeof(void*)*2);
lean_dec(v___y_751_);
v___y_746_ = v_hash_753_;
goto v___jp_745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase___redArg(lean_object* v_s_755_, lean_object* v_origin_756_){
_start:
{
lean_object* v_smap_757_; lean_object* v_origins_758_; lean_object* v_erased_759_; lean_object* v_omap_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_770_; 
v_smap_757_ = lean_ctor_get(v_s_755_, 0);
v_origins_758_ = lean_ctor_get(v_s_755_, 1);
v_erased_759_ = lean_ctor_get(v_s_755_, 2);
v_omap_760_ = lean_ctor_get(v_s_755_, 3);
v_isSharedCheck_770_ = !lean_is_exclusive(v_s_755_);
if (v_isSharedCheck_770_ == 0)
{
v___x_762_ = v_s_755_;
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_omap_760_);
lean_inc(v_erased_759_);
lean_inc(v_origins_758_);
lean_inc(v_smap_757_);
lean_dec(v_s_755_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_764_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_origins_758_, v_origin_756_);
v___x_765_ = lean_box(0);
v___x_766_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(v_erased_759_, v_origin_756_, v___x_765_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 2, v___x_766_);
lean_ctor_set(v___x_762_, 1, v___x_764_);
v___x_768_ = v___x_762_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_smap_757_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v_omap_760_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase(lean_object* v_00_u03b1_771_, lean_object* v_s_772_, lean_object* v_origin_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_s_772_, v_origin_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(lean_object* v_00_u03b2_775_, lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_x_776_, v_x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___boxed(lean_object* v_00_u03b2_779_, lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(v_00_u03b2_779_, v_x_780_, v_x_781_);
lean_dec_ref(v_x_781_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1(lean_object* v_00_u03b2_783_, lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(v_x_784_, v_x_785_, v_x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(lean_object* v_00_u03b2_788_, lean_object* v_x_789_, size_t v_x_790_, lean_object* v_x_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_789_, v_x_790_, v_x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
size_t v_x_1157__boxed_797_; lean_object* v_res_798_; 
v_x_1157__boxed_797_ = lean_unbox_usize(v_x_795_);
lean_dec(v_x_795_);
v_res_798_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(v_00_u03b2_793_, v_x_794_, v_x_1157__boxed_797_, v_x_796_);
lean_dec_ref(v_x_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(lean_object* v_00_u03b2_799_, lean_object* v_x_800_, size_t v_x_801_, size_t v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_800_, v_x_801_, v_x_802_, v_x_803_, v_x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___boxed(lean_object* v_00_u03b2_806_, lean_object* v_x_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v_x_811_){
_start:
{
size_t v_x_1168__boxed_812_; size_t v_x_1169__boxed_813_; lean_object* v_res_814_; 
v_x_1168__boxed_812_ = lean_unbox_usize(v_x_808_);
lean_dec(v_x_808_);
v_x_1169__boxed_813_ = lean_unbox_usize(v_x_809_);
lean_dec(v_x_809_);
v_res_814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(v_00_u03b2_806_, v_x_807_, v_x_1168__boxed_812_, v_x_1169__boxed_813_, v_x_810_, v_x_811_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_815_, lean_object* v_n_816_, lean_object* v_k_817_, lean_object* v_v_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(v_n_816_, v_k_817_, v_v_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_820_, size_t v_depth_821_, lean_object* v_keys_822_, lean_object* v_vals_823_, lean_object* v_heq_824_, lean_object* v_i_825_, lean_object* v_entries_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_depth_821_, v_keys_822_, v_vals_823_, v_i_825_, v_entries_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_828_, lean_object* v_depth_829_, lean_object* v_keys_830_, lean_object* v_vals_831_, lean_object* v_heq_832_, lean_object* v_i_833_, lean_object* v_entries_834_){
_start:
{
size_t v_depth_boxed_835_; lean_object* v_res_836_; 
v_depth_boxed_835_ = lean_unbox_usize(v_depth_829_);
lean_dec(v_depth_829_);
v_res_836_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(v_00_u03b2_828_, v_depth_boxed_835_, v_keys_830_, v_vals_831_, v_heq_832_, v_i_833_, v_entries_834_);
lean_dec_ref(v_vals_831_);
lean_dec_ref(v_keys_830_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(v_x_838_, v_x_839_, v_x_840_, v_x_841_);
return v___x_842_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_isErased___redArg(lean_object* v_s_843_, lean_object* v_origin_844_){
_start:
{
lean_object* v_erased_845_; uint8_t v___x_846_; 
v_erased_845_ = lean_ctor_get(v_s_843_, 2);
lean_inc_ref(v_erased_845_);
lean_dec_ref(v_s_843_);
v___x_846_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_erased_845_, v_origin_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___redArg___boxed(lean_object* v_s_847_, lean_object* v_origin_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_Lean_Meta_Grind_Theorems_isErased___redArg(v_s_847_, v_origin_848_);
lean_dec_ref(v_origin_848_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_isErased(lean_object* v_00_u03b1_851_, lean_object* v_s_852_, lean_object* v_origin_853_){
_start:
{
uint8_t v___x_854_; 
v___x_854_ = l_Lean_Meta_Grind_Theorems_isErased___redArg(v_s_852_, v_origin_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___boxed(lean_object* v_00_u03b1_855_, lean_object* v_s_856_, lean_object* v_origin_857_){
_start:
{
uint8_t v_res_858_; lean_object* v_r_859_; 
v_res_858_ = l_Lean_Meta_Grind_Theorems_isErased(v_00_u03b1_855_, v_s_856_, v_origin_857_);
lean_dec_ref(v_origin_857_);
v_r_859_ = lean_box(v_res_858_);
return v_r_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f___redArg(lean_object* v_s_860_, lean_object* v_sym_861_){
_start:
{
lean_object* v_smap_862_; lean_object* v_origins_863_; lean_object* v_erased_864_; lean_object* v_omap_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_886_; 
v_smap_862_ = lean_ctor_get(v_s_860_, 0);
v_origins_863_ = lean_ctor_get(v_s_860_, 1);
v_erased_864_ = lean_ctor_get(v_s_860_, 2);
v_omap_865_ = lean_ctor_get(v_s_860_, 3);
v_isSharedCheck_886_ = !lean_is_exclusive(v_s_860_);
if (v_isSharedCheck_886_ == 0)
{
v___x_867_ = v_s_860_;
v_isShared_868_ = v_isSharedCheck_886_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_omap_865_);
lean_inc(v_erased_864_);
lean_inc(v_origins_863_);
lean_inc(v_smap_862_);
lean_dec(v_s_860_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_886_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_870_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_861_);
lean_inc_ref(v_smap_862_);
v___x_871_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_869_, v___x_870_, v_smap_862_, v_sym_861_);
if (lean_obj_tag(v___x_871_) == 1)
{
lean_object* v_val_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_884_; 
v_val_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_884_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_884_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_val_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_884_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = l_Lean_PersistentHashMap_erase___redArg(v___x_869_, v___x_870_, v_smap_862_, v_sym_861_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_876_);
v___x_878_ = v___x_867_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_origins_863_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_erased_864_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v_omap_865_);
v___x_878_ = v_reuseFailAlloc_883_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v_val_872_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_879_);
v___x_881_ = v___x_874_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
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
else
{
lean_object* v___x_885_; 
lean_dec(v___x_871_);
lean_del_object(v___x_867_);
lean_dec_ref(v_omap_865_);
lean_dec_ref(v_erased_864_);
lean_dec_ref(v_origins_863_);
lean_dec_ref(v_smap_862_);
lean_dec(v_sym_861_);
v___x_885_ = lean_box(0);
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f(lean_object* v_00_u03b1_887_, lean_object* v_s_888_, lean_object* v_sym_889_){
_start:
{
lean_object* v_smap_890_; lean_object* v_origins_891_; lean_object* v_erased_892_; lean_object* v_omap_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_914_; 
v_smap_890_ = lean_ctor_get(v_s_888_, 0);
v_origins_891_ = lean_ctor_get(v_s_888_, 1);
v_erased_892_ = lean_ctor_get(v_s_888_, 2);
v_omap_893_ = lean_ctor_get(v_s_888_, 3);
v_isSharedCheck_914_ = !lean_is_exclusive(v_s_888_);
if (v_isSharedCheck_914_ == 0)
{
v___x_895_ = v_s_888_;
v_isShared_896_ = v_isSharedCheck_914_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_omap_893_);
lean_inc(v_erased_892_);
lean_inc(v_origins_891_);
lean_inc(v_smap_890_);
lean_dec(v_s_888_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_914_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_898_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_889_);
lean_inc_ref(v_smap_890_);
v___x_899_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_897_, v___x_898_, v_smap_890_, v_sym_889_);
if (lean_obj_tag(v___x_899_) == 1)
{
lean_object* v_val_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_912_; 
v_val_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_912_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_val_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = l_Lean_PersistentHashMap_erase___redArg(v___x_897_, v___x_898_, v_smap_890_, v_sym_889_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_904_);
v___x_906_ = v___x_895_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_origins_891_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_erased_892_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v_omap_893_);
v___x_906_ = v_reuseFailAlloc_911_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v_val_900_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_907_);
v___x_909_ = v___x_902_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v___x_913_; 
lean_dec(v___x_899_);
lean_del_object(v___x_895_);
lean_dec_ref(v_omap_893_);
lean_dec_ref(v_erased_892_);
lean_dec_ref(v_origins_891_);
lean_dec_ref(v_smap_890_);
lean_dec(v_sym_889_);
v___x_913_ = lean_box(0);
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_915_, lean_object* v_vals_916_, lean_object* v_i_917_, lean_object* v_k_918_){
_start:
{
lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = lean_array_get_size(v_keys_915_);
v___x_929_ = lean_nat_dec_lt(v_i_917_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_dec(v_i_917_);
v___x_930_ = lean_box(0);
return v___x_930_;
}
else
{
lean_object* v_k_x27_931_; lean_object* v___y_933_; lean_object* v_declName_935_; 
v_k_x27_931_ = lean_array_fget_borrowed(v_keys_915_, v_i_917_);
v_declName_935_ = lean_ctor_get(v_k_918_, 0);
v___y_933_ = v_declName_935_;
goto v___jp_932_;
v___jp_932_:
{
lean_object* v_declName_934_; 
v_declName_934_ = lean_ctor_get(v_k_x27_931_, 0);
lean_inc(v_declName_934_);
v___y_920_ = v___y_933_;
v___y_921_ = v_declName_934_;
goto v___jp_919_;
}
}
v___jp_919_:
{
uint8_t v___x_922_; 
v___x_922_ = lean_name_eq(v___y_920_, v___y_921_);
lean_dec(v___y_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_nat_add(v_i_917_, v___x_923_);
lean_dec(v_i_917_);
v_i_917_ = v___x_924_;
goto _start;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_array_fget_borrowed(v_vals_916_, v_i_917_);
lean_dec(v_i_917_);
lean_inc(v___x_926_);
v___x_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_936_, lean_object* v_vals_937_, lean_object* v_i_938_, lean_object* v_k_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_keys_936_, v_vals_937_, v_i_938_, v_k_939_);
lean_dec_ref(v_k_939_);
lean_dec_ref(v_vals_937_);
lean_dec_ref(v_keys_936_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(lean_object* v_x_941_, size_t v_x_942_, lean_object* v_x_943_){
_start:
{
if (lean_obj_tag(v_x_941_) == 0)
{
lean_object* v_es_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_972_; 
v_es_944_ = lean_ctor_get(v_x_941_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v_x_941_);
if (v_isSharedCheck_972_ == 0)
{
v___x_946_ = v_x_941_;
v_isShared_947_ = v_isSharedCheck_972_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_es_944_);
lean_dec(v_x_941_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_972_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; size_t v___x_949_; size_t v___x_950_; size_t v___x_951_; lean_object* v_j_952_; lean_object* v___x_953_; 
v___x_948_ = lean_box(2);
v___x_949_ = ((size_t)5ULL);
v___x_950_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___closed__1);
v___x_951_ = lean_usize_land(v_x_942_, v___x_950_);
v_j_952_ = lean_usize_to_nat(v___x_951_);
v___x_953_ = lean_array_get(v___x_948_, v_es_944_, v_j_952_);
lean_dec(v_j_952_);
lean_dec_ref(v_es_944_);
switch(lean_obj_tag(v___x_953_))
{
case 0:
{
lean_object* v_key_954_; lean_object* v_val_955_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_965_; lean_object* v_declName_967_; 
v_key_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_key_954_);
v_val_955_ = lean_ctor_get(v___x_953_, 1);
lean_inc(v_val_955_);
lean_dec_ref(v___x_953_);
v_declName_967_ = lean_ctor_get(v_x_943_, 0);
v___y_965_ = v_declName_967_;
goto v___jp_964_;
v___jp_956_:
{
uint8_t v___x_959_; 
v___x_959_ = lean_name_eq(v___y_957_, v___y_958_);
lean_dec(v___y_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_dec(v_val_955_);
lean_del_object(v___x_946_);
v___x_960_ = lean_box(0);
return v___x_960_;
}
else
{
lean_object* v___x_962_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 1);
lean_ctor_set(v___x_946_, 0, v_val_955_);
v___x_962_ = v___x_946_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_val_955_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
v___jp_964_:
{
lean_object* v_declName_966_; 
v_declName_966_ = lean_ctor_get(v_key_954_, 0);
lean_inc(v_declName_966_);
lean_dec(v_key_954_);
v___y_957_ = v___y_965_;
v___y_958_ = v_declName_966_;
goto v___jp_956_;
}
}
case 1:
{
lean_object* v_node_968_; size_t v___x_969_; 
lean_del_object(v___x_946_);
v_node_968_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_node_968_);
lean_dec_ref(v___x_953_);
v___x_969_ = lean_usize_shift_right(v_x_942_, v___x_949_);
v_x_941_ = v_node_968_;
v_x_942_ = v___x_969_;
goto _start;
}
default: 
{
lean_object* v___x_971_; 
lean_del_object(v___x_946_);
v___x_971_ = lean_box(0);
return v___x_971_;
}
}
}
}
else
{
lean_object* v_ks_973_; lean_object* v_vs_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_ks_973_ = lean_ctor_get(v_x_941_, 0);
lean_inc_ref(v_ks_973_);
v_vs_974_ = lean_ctor_get(v_x_941_, 1);
lean_inc_ref(v_vs_974_);
lean_dec_ref(v_x_941_);
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_ks_973_, v_vs_974_, v___x_975_, v_x_943_);
lean_dec_ref(v_vs_974_);
lean_dec_ref(v_ks_973_);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg___boxed(lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
size_t v_x_238__boxed_980_; lean_object* v_res_981_; 
v_x_238__boxed_980_ = lean_unbox_usize(v_x_978_);
lean_dec(v_x_978_);
v_res_981_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_977_, v_x_238__boxed_980_, v_x_979_);
lean_dec_ref(v_x_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(lean_object* v_x_982_, lean_object* v_x_983_){
_start:
{
uint64_t v___y_985_; lean_object* v___y_989_; lean_object* v_declName_992_; 
v_declName_992_ = lean_ctor_get(v_x_983_, 0);
v___y_989_ = v_declName_992_;
goto v___jp_988_;
v___jp_984_:
{
size_t v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_uint64_to_usize(v___y_985_);
v___x_987_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_982_, v___x_986_, v_x_983_);
return v___x_987_;
}
v___jp_988_:
{
if (lean_obj_tag(v___y_989_) == 0)
{
uint64_t v___x_990_; 
v___x_990_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0, &l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0);
v___y_985_ = v___x_990_;
goto v___jp_984_;
}
else
{
uint64_t v_hash_991_; 
v_hash_991_ = lean_ctor_get_uint64(v___y_989_, sizeof(void*)*2);
v___y_985_ = v_hash_991_;
goto v___jp_984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg___boxed(lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_x_993_, v_x_994_);
lean_dec_ref(v_x_994_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg(lean_object* v_s_996_, lean_object* v_origin_997_){
_start:
{
lean_object* v_omap_998_; lean_object* v___x_999_; 
v_omap_998_ = lean_ctor_get(v_s_996_, 3);
lean_inc_ref(v_omap_998_);
lean_dec_ref(v_s_996_);
v___x_999_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_omap_998_, v_origin_997_);
if (lean_obj_tag(v___x_999_) == 1)
{
lean_object* v_val_1000_; 
v_val_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_val_1000_);
lean_dec_ref(v___x_999_);
return v_val_1000_;
}
else
{
lean_object* v___x_1001_; 
lean_dec(v___x_999_);
v___x_1001_ = lean_box(0);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg___boxed(lean_object* v_s_1002_, lean_object* v_origin_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_s_1002_, v_origin_1003_);
lean_dec_ref(v_origin_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find(lean_object* v_00_u03b1_1005_, lean_object* v_s_1006_, lean_object* v_origin_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_s_1006_, v_origin_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___boxed(lean_object* v_00_u03b1_1009_, lean_object* v_s_1010_, lean_object* v_origin_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Meta_Grind_Theorems_find(v_00_u03b1_1009_, v_s_1010_, v_origin_1011_);
lean_dec_ref(v_origin_1011_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(lean_object* v_00_u03b2_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_x_1014_, v_x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___boxed(lean_object* v_00_u03b2_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(v_00_u03b2_1017_, v_x_1018_, v_x_1019_);
lean_dec_ref(v_x_1019_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(lean_object* v_00_u03b2_1021_, lean_object* v_x_1022_, size_t v_x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_1022_, v_x_1023_, v_x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
size_t v_x_366__boxed_1030_; lean_object* v_res_1031_; 
v_x_366__boxed_1030_ = lean_unbox_usize(v_x_1028_);
lean_dec(v_x_1028_);
v_res_1031_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(v_00_u03b2_1026_, v_x_1027_, v_x_366__boxed_1030_, v_x_1029_);
lean_dec_ref(v_x_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1032_, lean_object* v_keys_1033_, lean_object* v_vals_1034_, lean_object* v_heq_1035_, lean_object* v_i_1036_, lean_object* v_k_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_keys_1033_, v_vals_1034_, v_i_1036_, v_k_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1039_, lean_object* v_keys_1040_, lean_object* v_vals_1041_, lean_object* v_heq_1042_, lean_object* v_i_1043_, lean_object* v_k_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(v_00_u03b2_1039_, v_keys_1040_, v_vals_1041_, v_heq_1042_, v_i_1043_, v_k_1044_);
lean_dec_ref(v_k_1044_);
lean_dec_ref(v_vals_1041_);
lean_dec_ref(v_keys_1040_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(lean_object* v_x_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0___boxed(lean_object* v_x_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(v_x_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v_x_1053_);
return v_res_1059_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1);
v___x_1063_ = l_ReaderT_instMonad___redArg(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___f_1069_; 
v___x_1068_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1069_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1069_, 0, v___x_1068_);
return v___f_1069_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___f_1071_; 
v___x_1070_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1071_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1071_, 0, v___x_1070_);
return v___f_1071_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9(void){
_start:
{
lean_object* v___f_1072_; lean_object* v___f_1073_; lean_object* v___x_1074_; 
v___f_1072_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8);
v___f_1073_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___f_1073_);
lean_ctor_set(v___x_1074_, 1, v___f_1072_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___f_1076_; 
v___x_1075_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9);
v___f_1076_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1076_, 0, v___x_1075_);
return v___f_1076_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___f_1078_; 
v___x_1077_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9);
v___f_1078_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1078_, 0, v___x_1077_);
return v___f_1078_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12(void){
_start:
{
lean_object* v___f_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; 
v___f_1079_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11);
v___f_1080_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___f_1080_);
lean_ctor_set(v___x_1081_, 1, v___f_1079_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___f_1087_; lean_object* v___x_1088_; 
v___x_1085_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1086_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15));
v___f_1087_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13));
v___x_1088_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1087_, v___x_1086_, v___x_1085_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___f_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; 
v___x_1089_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16);
v___f_1090_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14));
v___f_1091_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13));
v___x_1092_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1091_, v___f_1090_, v___x_1089_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(lean_object* v_inst_1093_, lean_object* v_thm_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_getProof_1100_; lean_object* v_getLevelParams_1101_; lean_object* v___f_1102_; lean_object* v_proof_1103_; lean_object* v_us_1104_; uint8_t v___y_1106_; uint8_t v___x_1281_; 
v_getProof_1100_ = lean_ctor_get(v_inst_1093_, 3);
lean_inc_ref(v_getProof_1100_);
v_getLevelParams_1101_ = lean_ctor_get(v_inst_1093_, 4);
lean_inc_ref(v_getLevelParams_1101_);
lean_dec_ref(v_inst_1093_);
v___f_1102_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0));
lean_inc(v_thm_1094_);
v_proof_1103_ = lean_apply_1(v_getProof_1100_, v_thm_1094_);
v_us_1104_ = lean_apply_1(v_getLevelParams_1101_, v_thm_1094_);
v___x_1281_ = l_Lean_Expr_isConst(v_proof_1103_);
if (v___x_1281_ == 0)
{
v___y_1106_ = v___x_1281_;
goto v___jp_1105_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1282_ = lean_array_get_size(v_us_1104_);
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = lean_nat_dec_eq(v___x_1282_, v___x_1283_);
v___y_1106_ = v___x_1284_;
goto v___jp_1105_;
}
v___jp_1105_:
{
if (v___y_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1107_ = lean_array_get_size(v_us_1104_);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_nat_dec_eq(v___x_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; lean_object* v_toApplicative_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1189_; 
v___x_1110_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2);
v_toApplicative_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v___x_1110_, 1);
lean_dec(v_unused_1190_);
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1189_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_toApplicative_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1189_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_toFunctor_1115_; lean_object* v_toSeq_1116_; lean_object* v_toSeqLeft_1117_; lean_object* v_toSeqRight_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1187_; 
v_toFunctor_1115_ = lean_ctor_get(v_toApplicative_1111_, 0);
v_toSeq_1116_ = lean_ctor_get(v_toApplicative_1111_, 2);
v_toSeqLeft_1117_ = lean_ctor_get(v_toApplicative_1111_, 3);
v_toSeqRight_1118_ = lean_ctor_get(v_toApplicative_1111_, 4);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_toApplicative_1111_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v_toApplicative_1111_, 1);
lean_dec(v_unused_1188_);
v___x_1120_ = v_toApplicative_1111_;
v_isShared_1121_ = v_isSharedCheck_1187_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_toSeqRight_1118_);
lean_inc(v_toSeqLeft_1117_);
lean_inc(v_toSeq_1116_);
lean_inc(v_toFunctor_1115_);
lean_dec(v_toApplicative_1111_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1187_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___f_1122_; lean_object* v___f_1123_; lean_object* v___f_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; lean_object* v___f_1129_; lean_object* v___x_1131_; 
v___f_1122_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3));
v___f_1123_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4));
lean_inc_ref(v_toFunctor_1115_);
v___f_1124_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1124_, 0, v_toFunctor_1115_);
v___f_1125_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1125_, 0, v_toFunctor_1115_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___f_1124_);
lean_ctor_set(v___x_1126_, 1, v___f_1125_);
v___f_1127_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1127_, 0, v_toSeqRight_1118_);
v___f_1128_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1128_, 0, v_toSeqLeft_1117_);
v___f_1129_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1129_, 0, v_toSeq_1116_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v___f_1127_);
lean_ctor_set(v___x_1120_, 3, v___f_1128_);
lean_ctor_set(v___x_1120_, 2, v___f_1129_);
lean_ctor_set(v___x_1120_, 1, v___f_1122_);
lean_ctor_set(v___x_1120_, 0, v___x_1126_);
v___x_1131_ = v___x_1120_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___f_1122_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v___f_1129_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v___f_1128_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v___f_1127_);
v___x_1131_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v___f_1123_);
lean_ctor_set(v___x_1113_, 0, v___x_1131_);
v___x_1133_ = v___x_1113_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v___f_1123_);
v___x_1133_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v_toApplicative_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1183_; 
v___x_1134_ = l_ReaderT_instMonad___redArg(v___x_1133_);
v_toApplicative_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; 
v_unused_1184_ = lean_ctor_get(v___x_1134_, 1);
lean_dec(v_unused_1184_);
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1183_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_toApplicative_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1183_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_toFunctor_1139_; lean_object* v_toSeq_1140_; lean_object* v_toSeqLeft_1141_; lean_object* v_toSeqRight_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1181_; 
v_toFunctor_1139_ = lean_ctor_get(v_toApplicative_1135_, 0);
v_toSeq_1140_ = lean_ctor_get(v_toApplicative_1135_, 2);
v_toSeqLeft_1141_ = lean_ctor_get(v_toApplicative_1135_, 3);
v_toSeqRight_1142_ = lean_ctor_get(v_toApplicative_1135_, 4);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_toApplicative_1135_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v_toApplicative_1135_, 1);
lean_dec(v_unused_1182_);
v___x_1144_ = v_toApplicative_1135_;
v_isShared_1145_ = v_isSharedCheck_1181_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_toSeqRight_1142_);
lean_inc(v_toSeqLeft_1141_);
lean_inc(v_toSeq_1140_);
lean_inc(v_toFunctor_1139_);
lean_dec(v_toApplicative_1135_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1181_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___f_1146_; lean_object* v___f_1147_; lean_object* v___f_1148_; lean_object* v___f_1149_; lean_object* v___x_1150_; lean_object* v___f_1151_; lean_object* v___f_1152_; lean_object* v___f_1153_; lean_object* v___x_1155_; 
v___f_1146_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5));
v___f_1147_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6));
lean_inc_ref(v_toFunctor_1139_);
v___f_1148_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1148_, 0, v_toFunctor_1139_);
v___f_1149_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1149_, 0, v_toFunctor_1139_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___f_1148_);
lean_ctor_set(v___x_1150_, 1, v___f_1149_);
v___f_1151_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1151_, 0, v_toSeqRight_1142_);
v___f_1152_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1152_, 0, v_toSeqLeft_1141_);
v___f_1153_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1153_, 0, v_toSeq_1140_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 4, v___f_1151_);
lean_ctor_set(v___x_1144_, 3, v___f_1152_);
lean_ctor_set(v___x_1144_, 2, v___f_1153_);
lean_ctor_set(v___x_1144_, 1, v___f_1146_);
lean_ctor_set(v___x_1144_, 0, v___x_1150_);
v___x_1155_ = v___x_1144_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___f_1146_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v___f_1153_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v___f_1152_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v___f_1151_);
v___x_1155_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___f_1147_);
lean_ctor_set(v___x_1137_, 0, v___x_1155_);
v___x_1157_ = v___x_1137_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___f_1147_);
v___x_1157_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
size_t v_sz_1158_; size_t v___x_1159_; lean_object* v___x_995__overap_1160_; lean_object* v___x_1161_; 
v_sz_1158_ = lean_array_size(v_us_1104_);
v___x_1159_ = ((size_t)0ULL);
lean_inc_ref(v_us_1104_);
v___x_995__overap_1160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1157_, v___f_1102_, v_sz_1158_, v___x_1159_, v_us_1104_);
v___x_1161_ = lean_apply_5(v___x_995__overap_1160_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, lean_box(0));
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1170_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = l_Lean_Expr_instantiateLevelParamsArray(v_proof_1103_, v_us_1104_, v_a_1162_);
lean_dec_ref(v_proof_1103_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v_us_1104_);
lean_dec_ref(v_proof_1103_);
v_a_1171_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1161_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1161_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
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
lean_object* v___x_1191_; 
lean_dec_ref(v_us_1104_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_proof_1103_);
return v___x_1191_;
}
}
else
{
lean_object* v___x_1192_; lean_object* v_toApplicative_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_us_1104_);
v___x_1192_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2);
v_toApplicative_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v___x_1192_, 1);
lean_dec(v_unused_1280_);
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1279_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_toApplicative_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1279_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_toFunctor_1197_; lean_object* v_toSeq_1198_; lean_object* v_toSeqLeft_1199_; lean_object* v_toSeqRight_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1277_; 
v_toFunctor_1197_ = lean_ctor_get(v_toApplicative_1193_, 0);
v_toSeq_1198_ = lean_ctor_get(v_toApplicative_1193_, 2);
v_toSeqLeft_1199_ = lean_ctor_get(v_toApplicative_1193_, 3);
v_toSeqRight_1200_ = lean_ctor_get(v_toApplicative_1193_, 4);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_toApplicative_1193_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v_toApplicative_1193_, 1);
lean_dec(v_unused_1278_);
v___x_1202_ = v_toApplicative_1193_;
v_isShared_1203_ = v_isSharedCheck_1277_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_toSeqRight_1200_);
lean_inc(v_toSeqLeft_1199_);
lean_inc(v_toSeq_1198_);
lean_inc(v_toFunctor_1197_);
lean_dec(v_toApplicative_1193_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1277_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___x_1213_; 
v___f_1204_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3));
v___f_1205_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4));
lean_inc_ref(v_toFunctor_1197_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toFunctor_1197_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toFunctor_1197_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___f_1206_);
lean_ctor_set(v___x_1208_, 1, v___f_1207_);
v___f_1209_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1209_, 0, v_toSeqRight_1200_);
v___f_1210_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1210_, 0, v_toSeqLeft_1199_);
v___f_1211_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1211_, 0, v_toSeq_1198_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 4, v___f_1209_);
lean_ctor_set(v___x_1202_, 3, v___f_1210_);
lean_ctor_set(v___x_1202_, 2, v___f_1211_);
lean_ctor_set(v___x_1202_, 1, v___f_1204_);
lean_ctor_set(v___x_1202_, 0, v___x_1208_);
v___x_1213_ = v___x_1202_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___f_1204_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v___f_1211_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v___f_1210_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v___f_1209_);
v___x_1213_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v___f_1205_);
lean_ctor_set(v___x_1195_, 0, v___x_1213_);
v___x_1215_ = v___x_1195_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v___f_1205_);
v___x_1215_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; lean_object* v_toApplicative_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1273_; 
v___x_1216_ = l_ReaderT_instMonad___redArg(v___x_1215_);
v_toApplicative_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1273_ == 0)
{
lean_object* v_unused_1274_; 
v_unused_1274_ = lean_ctor_get(v___x_1216_, 1);
lean_dec(v_unused_1274_);
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1273_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_toApplicative_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1273_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_toFunctor_1221_; lean_object* v_toSeq_1222_; lean_object* v_toSeqLeft_1223_; lean_object* v_toSeqRight_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1271_; 
v_toFunctor_1221_ = lean_ctor_get(v_toApplicative_1217_, 0);
v_toSeq_1222_ = lean_ctor_get(v_toApplicative_1217_, 2);
v_toSeqLeft_1223_ = lean_ctor_get(v_toApplicative_1217_, 3);
v_toSeqRight_1224_ = lean_ctor_get(v_toApplicative_1217_, 4);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_toApplicative_1217_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v_toApplicative_1217_, 1);
lean_dec(v_unused_1272_);
v___x_1226_ = v_toApplicative_1217_;
v_isShared_1227_ = v_isSharedCheck_1271_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_toSeqRight_1224_);
lean_inc(v_toSeqLeft_1223_);
lean_inc(v_toSeq_1222_);
lean_inc(v_toFunctor_1221_);
lean_dec(v_toApplicative_1217_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1271_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___f_1228_; lean_object* v___f_1229_; lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; lean_object* v___f_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___x_1237_; 
v___f_1228_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5));
v___f_1229_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6));
lean_inc_ref(v_toFunctor_1221_);
v___f_1230_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1230_, 0, v_toFunctor_1221_);
v___f_1231_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1231_, 0, v_toFunctor_1221_);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___f_1230_);
lean_ctor_set(v___x_1232_, 1, v___f_1231_);
v___f_1233_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1233_, 0, v_toSeqRight_1224_);
v___f_1234_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1234_, 0, v_toSeqLeft_1223_);
v___f_1235_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1235_, 0, v_toSeq_1222_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 4, v___f_1233_);
lean_ctor_set(v___x_1226_, 3, v___f_1234_);
lean_ctor_set(v___x_1226_, 2, v___f_1235_);
lean_ctor_set(v___x_1226_, 1, v___f_1228_);
lean_ctor_set(v___x_1226_, 0, v___x_1232_);
v___x_1237_ = v___x_1226_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v___f_1228_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v___f_1235_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v___f_1234_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v___f_1233_);
v___x_1237_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___f_1229_);
lean_ctor_set(v___x_1219_, 0, v___x_1237_);
v___x_1239_ = v___x_1219_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v___f_1229_);
v___x_1239_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v_toMonadRef_1243_; lean_object* v_declName_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_983__overap_1248_; lean_object* v___x_1249_; 
v___x_1240_ = l_Lean_Meta_instMonadEnvMetaM;
v___x_1241_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12);
v___x_1242_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17);
v_toMonadRef_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc_ref(v_toMonadRef_1243_);
v_declName_1244_ = l_Lean_Expr_constName_x21(v_proof_1103_);
v___x_1245_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_1239_);
v___x_1246_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_1245_, v___x_1239_);
v___x_1247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1241_);
lean_ctor_set(v___x_1247_, 1, v_toMonadRef_1243_);
lean_ctor_set(v___x_1247_, 2, v___x_1246_);
lean_inc(v_declName_1244_);
v___x_983__overap_1248_ = l_Lean_getConstVal___redArg(v___x_1239_, v___x_1240_, v___x_1247_, v_declName_1244_);
lean_inc(v_a_1098_);
lean_inc_ref(v_a_1097_);
lean_inc(v_a_1096_);
lean_inc_ref(v_a_1095_);
v___x_1249_ = lean_apply_5(v___x_983__overap_1248_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, lean_box(0));
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1260_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1260_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1260_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_levelParams_1254_; uint8_t v___x_1255_; 
v_levelParams_1254_ = lean_ctor_get(v_a_1250_, 1);
lean_inc(v_levelParams_1254_);
lean_dec(v_a_1250_);
v___x_1255_ = l_List_isEmpty___redArg(v_levelParams_1254_);
lean_dec(v_levelParams_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_del_object(v___x_1252_);
lean_dec_ref(v_proof_1103_);
v___x_1256_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_1244_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
lean_dec(v_a_1098_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
return v___x_1256_;
}
else
{
lean_object* v___x_1258_; 
lean_dec(v_declName_1244_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v_proof_1103_);
v___x_1258_ = v___x_1252_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_proof_1103_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_declName_1244_);
lean_dec_ref(v_proof_1103_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
v_a_1261_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1249_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1249_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___boxed(lean_object* v_inst_1285_, lean_object* v_thm_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(v_inst_1285_, v_thm_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels(lean_object* v_00_u03b1_1293_, lean_object* v_inst_1294_, lean_object* v_thm_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(v_inst_1294_, v_thm_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___boxed(lean_object* v_00_u03b1_1302_, lean_object* v_inst_1303_, lean_object* v_thm_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels(v_00_u03b1_1302_, v_inst_1303_, v_thm_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(lean_object* v_msgData_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v_env_1318_; lean_object* v___x_1319_; lean_object* v_mctx_1320_; lean_object* v_lctx_1321_; lean_object* v_options_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1317_ = lean_st_ref_get(v___y_1315_);
v_env_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc_ref(v_env_1318_);
lean_dec(v___x_1317_);
v___x_1319_ = lean_st_ref_get(v___y_1313_);
v_mctx_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc_ref(v_mctx_1320_);
lean_dec(v___x_1319_);
v_lctx_1321_ = lean_ctor_get(v___y_1312_, 2);
v_options_1322_ = lean_ctor_get(v___y_1314_, 2);
lean_inc_ref(v_options_1322_);
lean_inc_ref(v_lctx_1321_);
v___x_1323_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1323_, 0, v_env_1318_);
lean_ctor_set(v___x_1323_, 1, v_mctx_1320_);
lean_ctor_set(v___x_1323_, 2, v_lctx_1321_);
lean_ctor_set(v___x_1323_, 3, v_options_1322_);
v___x_1324_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v_msgData_1311_);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0___boxed(lean_object* v_msgData_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(v_msgData_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(lean_object* v_msg_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_ref_1339_; lean_object* v___x_1340_; lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1349_; 
v_ref_1339_ = lean_ctor_get(v___y_1336_, 5);
v___x_1340_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(v_msg_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
lean_inc(v_ref_1339_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_ref_1339_);
lean_ctor_set(v___x_1345_, 1, v_a_1341_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set_tag(v___x_1343_, 1);
lean_ctor_set(v___x_1343_, 0, v___x_1345_);
v___x_1347_ = v___x_1343_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg___boxed(lean_object* v_msg_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v_res_1356_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0));
v___x_1359_ = l_Lean_stringToMessageData(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2));
v___x_1362_ = l_Lean_stringToMessageData(v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(lean_object* v_declName_1363_, lean_object* v_00_u03b1_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1370_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1);
v___x_1371_ = 0;
v___x_1372_ = l_Lean_MessageData_ofConstName(v_declName_1363_, v___x_1371_);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1370_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v___x_1375_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___boxed(lean_object* v_declName_1377_, lean_object* v_00_u03b1_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1377_, v_00_u03b1_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(lean_object* v_s_1385_, uint8_t v___x_1386_, lean_object* v_as_1387_, size_t v_i_1388_, size_t v_stop_1389_){
_start:
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_usize_dec_eq(v_i_1388_, v_stop_1389_);
if (v___x_1390_ == 0)
{
uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1391_ = 1;
v___x_1392_ = lean_array_uget_borrowed(v_as_1387_, v_i_1388_);
lean_inc(v___x_1392_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_inc_ref(v_s_1385_);
v___x_1394_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_1385_, v___x_1393_);
lean_dec_ref(v___x_1393_);
if (v___x_1394_ == 0)
{
lean_dec_ref(v_s_1385_);
return v___x_1391_;
}
else
{
if (v___x_1386_ == 0)
{
size_t v___x_1395_; size_t v___x_1396_; 
v___x_1395_ = ((size_t)1ULL);
v___x_1396_ = lean_usize_add(v_i_1388_, v___x_1395_);
v_i_1388_ = v___x_1396_;
goto _start;
}
else
{
lean_dec_ref(v_s_1385_);
return v___x_1391_;
}
}
}
else
{
uint8_t v___x_1398_; 
lean_dec_ref(v_s_1385_);
v___x_1398_ = 0;
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg___boxed(lean_object* v_s_1399_, lean_object* v___x_1400_, lean_object* v_as_1401_, lean_object* v_i_1402_, lean_object* v_stop_1403_){
_start:
{
uint8_t v___x_3360__boxed_1404_; size_t v_i_boxed_1405_; size_t v_stop_boxed_1406_; uint8_t v_res_1407_; lean_object* v_r_1408_; 
v___x_3360__boxed_1404_ = lean_unbox(v___x_1400_);
v_i_boxed_1405_ = lean_unbox_usize(v_i_1402_);
lean_dec(v_i_1402_);
v_stop_boxed_1406_ = lean_unbox_usize(v_stop_1403_);
lean_dec(v_stop_1403_);
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1399_, v___x_3360__boxed_1404_, v_as_1401_, v_i_boxed_1405_, v_stop_boxed_1406_);
lean_dec_ref(v_as_1401_);
v_r_1408_ = lean_box(v_res_1407_);
return v_r_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(lean_object* v_as_1409_, size_t v_i_1410_, size_t v_stop_1411_, lean_object* v_b_1412_){
_start:
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_usize_dec_eq(v_i_1410_, v_stop_1411_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; size_t v___x_1417_; size_t v___x_1418_; 
v___x_1414_ = lean_array_uget_borrowed(v_as_1409_, v_i_1410_);
lean_inc(v___x_1414_);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
v___x_1416_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_b_1412_, v___x_1415_);
v___x_1417_ = ((size_t)1ULL);
v___x_1418_ = lean_usize_add(v_i_1410_, v___x_1417_);
v_i_1410_ = v___x_1418_;
v_b_1412_ = v___x_1416_;
goto _start;
}
else
{
return v_b_1412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg___boxed(lean_object* v_as_1420_, lean_object* v_i_1421_, lean_object* v_stop_1422_, lean_object* v_b_1423_){
_start:
{
size_t v_i_boxed_1424_; size_t v_stop_boxed_1425_; lean_object* v_res_1426_; 
v_i_boxed_1424_ = lean_unbox_usize(v_i_1421_);
lean_dec(v_i_1421_);
v_stop_boxed_1425_ = lean_unbox_usize(v_stop_1422_);
lean_dec(v_stop_1422_);
v_res_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_as_1420_, v_i_boxed_1424_, v_stop_boxed_1425_, v_b_1423_);
lean_dec_ref(v_as_1420_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object* v_s_1427_, lean_object* v_declName_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v___x_1438_; lean_object* v_env_1439_; uint8_t v___x_1440_; 
v___x_1438_ = lean_st_ref_get(v_a_1432_);
v_env_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_env_1439_);
lean_dec(v___x_1438_);
lean_inc(v_declName_1428_);
v___x_1440_ = l_Lean_wasOriginallyTheorem(v_env_1439_, v_declName_1428_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; 
lean_inc(v_a_1432_);
lean_inc_ref(v_a_1431_);
lean_inc(v_a_1430_);
lean_inc_ref(v_a_1429_);
lean_inc(v_declName_1428_);
v___x_1441_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1486_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1486_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1486_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
if (lean_obj_tag(v_a_1442_) == 1)
{
lean_object* v_val_1446_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v_val_1446_ = lean_ctor_get(v_a_1442_, 0);
lean_inc(v_val_1446_);
lean_dec_ref(v_a_1442_);
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = lean_array_get_size(v_val_1446_);
v___x_1472_ = lean_nat_dec_lt(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_declName_1428_);
goto v___jp_1447_;
}
else
{
if (v___x_1472_ == 0)
{
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_declName_1428_);
goto v___jp_1447_;
}
else
{
size_t v___x_1473_; size_t v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = ((size_t)0ULL);
v___x_1474_ = lean_usize_of_nat(v___x_1471_);
lean_inc_ref(v_s_1427_);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1427_, v___x_1440_, v_val_1446_, v___x_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_declName_1428_);
goto v___jp_1447_;
}
else
{
lean_object* v___x_1476_; lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_val_1446_);
lean_del_object(v___x_1444_);
lean_dec_ref(v_s_1427_);
v___x_1476_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1428_, lean_box(0), v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
v___jp_1447_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = lean_array_get_size(v_val_1446_);
v___x_1450_ = lean_nat_dec_lt(v___x_1448_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1452_; 
lean_dec(v_val_1446_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v_s_1427_);
v___x_1452_ = v___x_1444_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_s_1427_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
else
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_nat_dec_le(v___x_1449_, v___x_1449_);
if (v___x_1454_ == 0)
{
if (v___x_1450_ == 0)
{
lean_object* v___x_1456_; 
lean_dec(v_val_1446_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v_s_1427_);
v___x_1456_ = v___x_1444_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_s_1427_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
else
{
size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = lean_usize_of_nat(v___x_1449_);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_val_1446_, v___x_1458_, v___x_1459_, v_s_1427_);
lean_dec(v_val_1446_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1460_);
v___x_1462_ = v___x_1444_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
else
{
size_t v___x_1464_; size_t v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1464_ = ((size_t)0ULL);
v___x_1465_ = lean_usize_of_nat(v___x_1449_);
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_val_1446_, v___x_1464_, v___x_1465_, v_s_1427_);
lean_dec(v_val_1446_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1466_);
v___x_1468_ = v___x_1444_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
else
{
lean_object* v___x_1485_; 
lean_del_object(v___x_1444_);
lean_dec(v_a_1442_);
lean_dec_ref(v_s_1427_);
v___x_1485_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1428_, lean_box(0), v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
return v___x_1485_;
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_declName_1428_);
lean_dec_ref(v_s_1427_);
v_a_1487_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1441_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1441_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
lean_inc(v_declName_1428_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_declName_1428_);
lean_inc_ref(v_s_1427_);
v___x_1496_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_1427_, v___x_1495_);
lean_dec_ref(v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec_ref(v_s_1427_);
v___x_1497_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1428_, lean_box(0), v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
else
{
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
goto v___jp_1434_;
}
}
v___jp_1434_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_declName_1428_);
v___x_1436_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_s_1427_, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___boxed(lean_object* v_s_1506_, lean_object* v_declName_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_s_1506_, v_declName_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl(lean_object* v_00_u03b1_1514_, lean_object* v_s_1515_, lean_object* v_declName_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_s_1515_, v_declName_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___boxed(lean_object* v_00_u03b1_1523_, lean_object* v_s_1524_, lean_object* v_declName_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Meta_Grind_Theorems_eraseDecl(v_00_u03b1_1523_, v_s_1524_, v_declName_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(lean_object* v_00_u03b1_1532_, lean_object* v_msg_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___boxed(lean_object* v_00_u03b1_1540_, lean_object* v_msg_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(v_00_u03b1_1540_, v_msg_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(lean_object* v_00_u03b1_1548_, lean_object* v_as_1549_, size_t v_i_1550_, size_t v_stop_1551_, lean_object* v_b_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_as_1549_, v_i_1550_, v_stop_1551_, v_b_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___boxed(lean_object* v_00_u03b1_1554_, lean_object* v_as_1555_, lean_object* v_i_1556_, lean_object* v_stop_1557_, lean_object* v_b_1558_){
_start:
{
size_t v_i_boxed_1559_; size_t v_stop_boxed_1560_; lean_object* v_res_1561_; 
v_i_boxed_1559_ = lean_unbox_usize(v_i_1556_);
lean_dec(v_i_1556_);
v_stop_boxed_1560_ = lean_unbox_usize(v_stop_1557_);
lean_dec(v_stop_1557_);
v_res_1561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(v_00_u03b1_1554_, v_as_1555_, v_i_boxed_1559_, v_stop_boxed_1560_, v_b_1558_);
lean_dec_ref(v_as_1555_);
return v_res_1561_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(lean_object* v_00_u03b1_1562_, lean_object* v_s_1563_, uint8_t v___x_1564_, lean_object* v_as_1565_, size_t v_i_1566_, size_t v_stop_1567_){
_start:
{
uint8_t v___x_1568_; 
v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1563_, v___x_1564_, v_as_1565_, v_i_1566_, v_stop_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___boxed(lean_object* v_00_u03b1_1569_, lean_object* v_s_1570_, lean_object* v___x_1571_, lean_object* v_as_1572_, lean_object* v_i_1573_, lean_object* v_stop_1574_){
_start:
{
uint8_t v___x_3590__boxed_1575_; size_t v_i_boxed_1576_; size_t v_stop_boxed_1577_; uint8_t v_res_1578_; lean_object* v_r_1579_; 
v___x_3590__boxed_1575_ = lean_unbox(v___x_1571_);
v_i_boxed_1576_ = lean_unbox_usize(v_i_1573_);
lean_dec(v_i_1573_);
v_stop_boxed_1577_ = lean_unbox_usize(v_stop_1574_);
lean_dec(v_stop_1574_);
v_res_1578_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(v_00_u03b1_1569_, v_s_1570_, v___x_3590__boxed_1575_, v_as_1572_, v_i_boxed_1576_, v_stop_boxed_1577_);
lean_dec_ref(v_as_1572_);
v_r_1579_ = lean_box(v_res_1578_);
return v_r_1579_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
if (lean_obj_tag(v_a_1580_) == 0)
{
lean_object* v___x_1582_; 
v___x_1582_ = l_List_reverse___redArg(v_a_1581_);
return v___x_1582_;
}
else
{
lean_object* v_head_1583_; lean_object* v_tail_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1593_; 
v_head_1583_ = lean_ctor_get(v_a_1580_, 0);
v_tail_1584_ = lean_ctor_get(v_a_1580_, 1);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_a_1580_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1586_ = v_a_1580_;
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_tail_1584_);
lean_inc(v_head_1583_);
lean_dec(v_a_1580_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1593_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v_fst_1588_; lean_object* v___x_1590_; 
v_fst_1588_ = lean_ctor_get(v_head_1583_, 0);
lean_inc(v_fst_1588_);
lean_dec(v_head_1583_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v_a_1581_);
lean_ctor_set(v___x_1586_, 0, v_fst_1588_);
v___x_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_fst_1588_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_a_1581_);
v___x_1590_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
v_a_1580_ = v_tail_1584_;
v_a_1581_ = v___x_1590_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___lam__0(lean_object* v_ps_1594_, lean_object* v_k_1595_, lean_object* v_v_1596_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v_k_1595_);
lean_ctor_set(v___x_1597_, 1, v_v_1596_);
v___x_1598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v_ps_1594_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1599_, lean_object* v_x1_1600_, lean_object* v_x2_1601_, lean_object* v_x3_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_apply_3(v_f_1599_, v_x1_1600_, v_x2_1601_, v_x3_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_f_1604_, lean_object* v_keys_1605_, lean_object* v_vals_1606_, lean_object* v_i_1607_, lean_object* v_acc_1608_){
_start:
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = lean_array_get_size(v_keys_1605_);
v___x_1610_ = lean_nat_dec_lt(v_i_1607_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_dec(v_i_1607_);
lean_dec(v_f_1604_);
return v_acc_1608_;
}
else
{
lean_object* v_k_1611_; lean_object* v_v_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v_k_1611_ = lean_array_fget_borrowed(v_keys_1605_, v_i_1607_);
v_v_1612_ = lean_array_fget_borrowed(v_vals_1606_, v_i_1607_);
lean_inc(v_f_1604_);
lean_inc(v_v_1612_);
lean_inc(v_k_1611_);
v___x_1613_ = lean_apply_3(v_f_1604_, v_acc_1608_, v_k_1611_, v_v_1612_);
v___x_1614_ = lean_unsigned_to_nat(1u);
v___x_1615_ = lean_nat_add(v_i_1607_, v___x_1614_);
lean_dec(v_i_1607_);
v_i_1607_ = v___x_1615_;
v_acc_1608_ = v___x_1613_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_f_1617_, lean_object* v_keys_1618_, lean_object* v_vals_1619_, lean_object* v_i_1620_, lean_object* v_acc_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1617_, v_keys_1618_, v_vals_1619_, v_i_1620_, v_acc_1621_);
lean_dec_ref(v_vals_1619_);
lean_dec_ref(v_keys_1618_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_f_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
if (lean_obj_tag(v_x_1624_) == 0)
{
lean_object* v_es_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v_es_1626_ = lean_ctor_get(v_x_1624_, 0);
v___x_1627_ = lean_unsigned_to_nat(0u);
v___x_1628_ = lean_array_get_size(v_es_1626_);
v___x_1629_ = lean_nat_dec_lt(v___x_1627_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_dec(v_f_1623_);
return v_x_1625_;
}
else
{
uint8_t v___x_1630_; 
v___x_1630_ = lean_nat_dec_le(v___x_1628_, v___x_1628_);
if (v___x_1630_ == 0)
{
if (v___x_1629_ == 0)
{
lean_dec(v_f_1623_);
return v_x_1625_;
}
else
{
size_t v___x_1631_; size_t v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = lean_usize_of_nat(v___x_1628_);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1623_, v_es_1626_, v___x_1631_, v___x_1632_, v_x_1625_);
return v___x_1633_;
}
}
else
{
size_t v___x_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = ((size_t)0ULL);
v___x_1635_ = lean_usize_of_nat(v___x_1628_);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1623_, v_es_1626_, v___x_1634_, v___x_1635_, v_x_1625_);
return v___x_1636_;
}
}
}
else
{
lean_object* v_ks_1637_; lean_object* v_vs_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_ks_1637_ = lean_ctor_get(v_x_1624_, 0);
v_vs_1638_ = lean_ctor_get(v_x_1624_, 1);
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1623_, v_ks_1637_, v_vs_1638_, v___x_1639_, v_x_1625_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_f_1641_, lean_object* v_as_1642_, size_t v_i_1643_, size_t v_stop_1644_, lean_object* v_b_1645_){
_start:
{
lean_object* v___y_1647_; uint8_t v___x_1651_; 
v___x_1651_ = lean_usize_dec_eq(v_i_1643_, v_stop_1644_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_array_uget_borrowed(v_as_1642_, v_i_1643_);
switch(lean_obj_tag(v___x_1652_))
{
case 0:
{
lean_object* v_key_1653_; lean_object* v_val_1654_; lean_object* v___x_1655_; 
v_key_1653_ = lean_ctor_get(v___x_1652_, 0);
v_val_1654_ = lean_ctor_get(v___x_1652_, 1);
lean_inc(v_f_1641_);
lean_inc(v_val_1654_);
lean_inc(v_key_1653_);
v___x_1655_ = lean_apply_3(v_f_1641_, v_b_1645_, v_key_1653_, v_val_1654_);
v___y_1647_ = v___x_1655_;
goto v___jp_1646_;
}
case 1:
{
lean_object* v_node_1656_; lean_object* v___x_1657_; 
v_node_1656_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_f_1641_);
v___x_1657_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1641_, v_node_1656_, v_b_1645_);
v___y_1647_ = v___x_1657_;
goto v___jp_1646_;
}
default: 
{
v___y_1647_ = v_b_1645_;
goto v___jp_1646_;
}
}
}
else
{
lean_dec(v_f_1641_);
return v_b_1645_;
}
v___jp_1646_:
{
size_t v___x_1648_; size_t v___x_1649_; 
v___x_1648_ = ((size_t)1ULL);
v___x_1649_ = lean_usize_add(v_i_1643_, v___x_1648_);
v_i_1643_ = v___x_1649_;
v_b_1645_ = v___y_1647_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_f_1658_, lean_object* v_as_1659_, lean_object* v_i_1660_, lean_object* v_stop_1661_, lean_object* v_b_1662_){
_start:
{
size_t v_i_boxed_1663_; size_t v_stop_boxed_1664_; lean_object* v_res_1665_; 
v_i_boxed_1663_ = lean_unbox_usize(v_i_1660_);
lean_dec(v_i_1660_);
v_stop_boxed_1664_ = lean_unbox_usize(v_stop_1661_);
lean_dec(v_stop_1661_);
v_res_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1658_, v_as_1659_, v_i_boxed_1663_, v_stop_boxed_1664_, v_b_1662_);
lean_dec_ref(v_as_1659_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1666_, v_x_1667_, v_x_1668_);
lean_dec_ref(v_x_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(lean_object* v_map_1670_, lean_object* v_f_1671_, lean_object* v_init_1672_){
_start:
{
lean_object* v___f_1673_; lean_object* v___x_1674_; 
v___f_1673_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1673_, 0, v_f_1671_);
v___x_1674_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v___f_1673_, v_map_1670_, v_init_1672_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_1675_, lean_object* v_f_1676_, lean_object* v_init_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_map_1675_, v_f_1676_, v_init_1677_);
lean_dec_ref(v_map_1675_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(lean_object* v_m_1680_){
_start:
{
lean_object* v___f_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___f_1681_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0));
v___x_1682_ = lean_box(0);
v___x_1683_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_m_1680_, v___f_1681_, v___x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___boxed(lean_object* v_m_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_m_1684_);
lean_dec_ref(v_m_1684_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(lean_object* v_s_1686_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_s_1686_);
v___x_1688_ = lean_box(0);
v___x_1689_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(v___x_1687_, v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0___boxed(lean_object* v_s_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(v_s_1690_);
lean_dec_ref(v_s_1690_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg(lean_object* v_s_1692_){
_start:
{
lean_object* v_origins_1693_; lean_object* v___x_1694_; 
v_origins_1693_ = lean_ctor_get(v_s_1692_, 1);
v___x_1694_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(v_origins_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg___boxed(lean_object* v_s_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_s_1695_);
lean_dec_ref(v_s_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins(lean_object* v_00_u03b1_1697_, lean_object* v_s_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_s_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_s_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_Meta_Grind_Theorems_getOrigins(v_00_u03b1_1700_, v_s_1701_);
lean_dec_ref(v_s_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(lean_object* v_00_u03b2_1703_, lean_object* v_m_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_m_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1706_, lean_object* v_m_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(v_00_u03b2_1706_, v_m_1707_);
lean_dec_ref(v_m_1707_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1709_, lean_object* v_00_u03b2_1710_, lean_object* v_map_1711_, lean_object* v_f_1712_, lean_object* v_init_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_map_1711_, v_f_1712_, v_init_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1715_, lean_object* v_00_u03b2_1716_, lean_object* v_map_1717_, lean_object* v_f_1718_, lean_object* v_init_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(v_00_u03c3_1715_, v_00_u03b2_1716_, v_map_1717_, v_f_1718_, v_init_1719_);
lean_dec_ref(v_map_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1721_, lean_object* v_f_1722_, lean_object* v_init_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1722_, v_map_1721_, v_init_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1725_, lean_object* v_f_1726_, lean_object* v_init_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(v_map_1725_, v_f_1726_, v_init_1727_);
lean_dec_ref(v_map_1725_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1729_, lean_object* v_00_u03b2_1730_, lean_object* v_map_1731_, lean_object* v_f_1732_, lean_object* v_init_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1732_, v_map_1731_, v_init_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1735_, lean_object* v_00_u03b2_1736_, lean_object* v_map_1737_, lean_object* v_f_1738_, lean_object* v_init_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(v_00_u03c3_1735_, v_00_u03b2_1736_, v_map_1737_, v_f_1738_, v_init_1739_);
lean_dec_ref(v_map_1737_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1741_, lean_object* v_00_u03b1_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_f_1744_, lean_object* v_x_1745_, lean_object* v_x_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1744_, v_x_1745_, v_x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1748_, lean_object* v_00_u03b1_1749_, lean_object* v_00_u03b2_1750_, lean_object* v_f_1751_, lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03c3_1748_, v_00_u03b1_1749_, v_00_u03b2_1750_, v_f_1751_, v_x_1752_, v_x_1753_);
lean_dec_ref(v_x_1752_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_1755_, lean_object* v_00_u03b2_1756_, lean_object* v_00_u03c3_1757_, lean_object* v_f_1758_, lean_object* v_as_1759_, size_t v_i_1760_, size_t v_stop_1761_, lean_object* v_b_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1758_, v_as_1759_, v_i_1760_, v_stop_1761_, v_b_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_00_u03c3_1766_, lean_object* v_f_1767_, lean_object* v_as_1768_, lean_object* v_i_1769_, lean_object* v_stop_1770_, lean_object* v_b_1771_){
_start:
{
size_t v_i_boxed_1772_; size_t v_stop_boxed_1773_; lean_object* v_res_1774_; 
v_i_boxed_1772_ = lean_unbox_usize(v_i_1769_);
lean_dec(v_i_1769_);
v_stop_boxed_1773_ = lean_unbox_usize(v_stop_1770_);
lean_dec(v_stop_1770_);
v_res_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_00_u03b1_1764_, v_00_u03b2_1765_, v_00_u03c3_1766_, v_f_1767_, v_as_1768_, v_i_boxed_1772_, v_stop_boxed_1773_, v_b_1771_);
lean_dec_ref(v_as_1768_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03c3_1775_, lean_object* v_00_u03b1_1776_, lean_object* v_00_u03b2_1777_, lean_object* v_f_1778_, lean_object* v_keys_1779_, lean_object* v_vals_1780_, lean_object* v_heq_1781_, lean_object* v_i_1782_, lean_object* v_acc_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1778_, v_keys_1779_, v_vals_1780_, v_i_1782_, v_acc_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03c3_1785_, lean_object* v_00_u03b1_1786_, lean_object* v_00_u03b2_1787_, lean_object* v_f_1788_, lean_object* v_keys_1789_, lean_object* v_vals_1790_, lean_object* v_heq_1791_, lean_object* v_i_1792_, lean_object* v_acc_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03c3_1785_, v_00_u03b1_1786_, v_00_u03b2_1787_, v_f_1788_, v_keys_1789_, v_vals_1790_, v_heq_1791_, v_i_1792_, v_acc_1793_);
lean_dec_ref(v_vals_1790_);
lean_dec_ref(v_keys_1789_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty(lean_object* v_00_u03b1_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0(void){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems(lean_object* v_00_u03b1_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_obj_once(&l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0, &l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0_once, _init_l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
if (lean_obj_tag(v_a_1800_) == 0)
{
lean_object* v___x_1802_; 
v___x_1802_ = l_List_reverse___redArg(v_a_1801_);
return v___x_1802_;
}
else
{
lean_object* v_head_1803_; lean_object* v_tail_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1813_; 
v_head_1803_ = lean_ctor_get(v_a_1800_, 0);
v_tail_1804_ = lean_ctor_get(v_a_1800_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_a_1800_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1806_ = v_a_1800_;
v_isShared_1807_ = v_isSharedCheck_1813_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_tail_1804_);
lean_inc(v_head_1803_);
lean_dec(v_a_1800_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1813_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = l_Lean_mkLevelParam(v_head_1803_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 1, v_a_1801_);
lean_ctor_set(v___x_1806_, 0, v___x_1808_);
v___x_1810_ = v___x_1806_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_a_1801_);
v___x_1810_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
v_a_1800_ = v_tail_1804_;
v_a_1801_ = v___x_1810_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1814_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1819_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
lean_ctor_set(v___x_1819_, 2, v___x_1818_);
lean_ctor_set(v___x_1819_, 3, v___x_1817_);
lean_ctor_set(v___x_1819_, 4, v___x_1817_);
lean_ctor_set(v___x_1819_, 5, v___x_1817_);
lean_ctor_set(v___x_1819_, 6, v___x_1817_);
lean_ctor_set(v___x_1819_, 7, v___x_1817_);
lean_ctor_set(v___x_1819_, 8, v___x_1817_);
return v___x_1819_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = lean_unsigned_to_nat(32u);
v___x_1821_ = lean_mk_empty_array_with_capacity(v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1823_ = ((size_t)5ULL);
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = lean_unsigned_to_nat(32u);
v___x_1826_ = lean_mk_empty_array_with_capacity(v___x_1825_);
v___x_1827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1828_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1826_);
lean_ctor_set(v___x_1828_, 2, v___x_1824_);
lean_ctor_set(v___x_1828_, 3, v___x_1824_);
lean_ctor_set_usize(v___x_1828_, 4, v___x_1823_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1829_ = lean_box(1);
v___x_1830_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v___x_1830_);
lean_ctor_set(v___x_1832_, 2, v___x_1829_);
return v___x_1832_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1835_ = l_Lean_stringToMessageData(v___x_1834_);
return v___x_1835_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1838_ = l_Lean_stringToMessageData(v___x_1837_);
return v___x_1838_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1841_ = l_Lean_stringToMessageData(v___x_1840_);
return v___x_1841_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1844_ = l_Lean_stringToMessageData(v___x_1843_);
return v___x_1844_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1847_ = l_Lean_stringToMessageData(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1850_ = l_Lean_stringToMessageData(v___x_1849_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1853_ = l_Lean_stringToMessageData(v___x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1854_, lean_object* v_declHint_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; lean_object* v_env_1859_; uint8_t v___x_1860_; 
v___x_1858_ = lean_st_ref_get(v___y_1856_);
v_env_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc_ref(v_env_1859_);
lean_dec(v___x_1858_);
v___x_1860_ = l_Lean_Name_isAnonymous(v_declHint_1855_);
if (v___x_1860_ == 0)
{
uint8_t v_isExporting_1861_; 
v_isExporting_1861_ = lean_ctor_get_uint8(v_env_1859_, sizeof(void*)*8);
if (v_isExporting_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref(v_env_1859_);
lean_dec(v_declHint_1855_);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_msg_1854_);
return v___x_1862_;
}
else
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
lean_inc_ref(v_env_1859_);
v___x_1863_ = l_Lean_Environment_setExporting(v_env_1859_, v___x_1860_);
lean_inc(v_declHint_1855_);
lean_inc_ref(v___x_1863_);
v___x_1864_ = l_Lean_Environment_contains(v___x_1863_, v_declHint_1855_, v_isExporting_1861_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
lean_dec_ref(v___x_1863_);
lean_dec_ref(v_env_1859_);
lean_dec(v_declHint_1855_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v_msg_1854_);
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v_c_1871_; lean_object* v___x_1872_; 
v___x_1866_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1868_ = l_Lean_Options_empty;
v___x_1869_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1863_);
lean_ctor_set(v___x_1869_, 1, v___x_1866_);
lean_ctor_set(v___x_1869_, 2, v___x_1867_);
lean_ctor_set(v___x_1869_, 3, v___x_1868_);
lean_inc(v_declHint_1855_);
v___x_1870_ = l_Lean_MessageData_ofConstName(v_declHint_1855_, v___x_1860_);
v_c_1871_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1871_, 0, v___x_1869_);
lean_ctor_set(v_c_1871_, 1, v___x_1870_);
v___x_1872_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1859_, v_declHint_1855_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_dec_ref(v_env_1859_);
lean_dec(v_declHint_1855_);
v___x_1873_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v_c_1871_);
v___x_1875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = l_Lean_MessageData_note(v___x_1876_);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v_msg_1854_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
else
{
lean_object* v_val_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1915_; 
v_val_1880_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1882_ = v___x_1872_;
v_isShared_1883_ = v_isSharedCheck_1915_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_val_1880_);
lean_dec(v___x_1872_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1915_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v_mod_1887_; uint8_t v___x_1888_; 
v___x_1884_ = lean_box(0);
v___x_1885_ = l_Lean_Environment_header(v_env_1859_);
lean_dec_ref(v_env_1859_);
v___x_1886_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1885_);
v_mod_1887_ = lean_array_get(v___x_1884_, v___x_1886_, v_val_1880_);
lean_dec(v_val_1880_);
lean_dec_ref(v___x_1886_);
v___x_1888_ = l_Lean_isPrivateName(v_declHint_1855_);
lean_dec(v_declHint_1855_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v_c_1871_);
v___x_1891_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = l_Lean_MessageData_ofName(v_mod_1887_);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = l_Lean_MessageData_note(v___x_1896_);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v_msg_1854_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1898_);
v___x_1900_ = v___x_1882_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v_c_1871_);
v___x_1904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = l_Lean_MessageData_ofName(v_mod_1887_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = l_Lean_MessageData_note(v___x_1909_);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_msg_1854_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1911_);
v___x_1913_ = v___x_1882_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1916_; 
lean_dec_ref(v_env_1859_);
lean_dec(v_declHint_1855_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_msg_1854_);
return v___x_1916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1917_, lean_object* v_declHint_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_1917_, v_declHint_1918_, v___y_1919_);
lean_dec(v___y_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_1922_, lean_object* v_declHint_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1939_; 
v___x_1929_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_1922_, v_declHint_1923_, v___y_1927_);
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1939_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1939_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1934_ = l_Lean_unknownIdentifierMessageTag;
v___x_1935_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v_a_1930_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1935_);
v___x_1937_ = v___x_1932_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_1940_, lean_object* v_declHint_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_1940_, v_declHint_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_1948_, lean_object* v_msg_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_fileName_1955_; lean_object* v_fileMap_1956_; lean_object* v_options_1957_; lean_object* v_currRecDepth_1958_; lean_object* v_maxRecDepth_1959_; lean_object* v_ref_1960_; lean_object* v_currNamespace_1961_; lean_object* v_openDecls_1962_; lean_object* v_initHeartbeats_1963_; lean_object* v_maxHeartbeats_1964_; lean_object* v_quotContext_1965_; lean_object* v_currMacroScope_1966_; uint8_t v_diag_1967_; lean_object* v_cancelTk_x3f_1968_; uint8_t v_suppressElabErrors_1969_; lean_object* v_inheritedTraceOptions_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1979_; 
v_fileName_1955_ = lean_ctor_get(v___y_1952_, 0);
v_fileMap_1956_ = lean_ctor_get(v___y_1952_, 1);
v_options_1957_ = lean_ctor_get(v___y_1952_, 2);
v_currRecDepth_1958_ = lean_ctor_get(v___y_1952_, 3);
v_maxRecDepth_1959_ = lean_ctor_get(v___y_1952_, 4);
v_ref_1960_ = lean_ctor_get(v___y_1952_, 5);
v_currNamespace_1961_ = lean_ctor_get(v___y_1952_, 6);
v_openDecls_1962_ = lean_ctor_get(v___y_1952_, 7);
v_initHeartbeats_1963_ = lean_ctor_get(v___y_1952_, 8);
v_maxHeartbeats_1964_ = lean_ctor_get(v___y_1952_, 9);
v_quotContext_1965_ = lean_ctor_get(v___y_1952_, 10);
v_currMacroScope_1966_ = lean_ctor_get(v___y_1952_, 11);
v_diag_1967_ = lean_ctor_get_uint8(v___y_1952_, sizeof(void*)*14);
v_cancelTk_x3f_1968_ = lean_ctor_get(v___y_1952_, 12);
v_suppressElabErrors_1969_ = lean_ctor_get_uint8(v___y_1952_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1970_ = lean_ctor_get(v___y_1952_, 13);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___y_1952_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1972_ = v___y_1952_;
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_inheritedTraceOptions_1970_);
lean_inc(v_cancelTk_x3f_1968_);
lean_inc(v_currMacroScope_1966_);
lean_inc(v_quotContext_1965_);
lean_inc(v_maxHeartbeats_1964_);
lean_inc(v_initHeartbeats_1963_);
lean_inc(v_openDecls_1962_);
lean_inc(v_currNamespace_1961_);
lean_inc(v_ref_1960_);
lean_inc(v_maxRecDepth_1959_);
lean_inc(v_currRecDepth_1958_);
lean_inc(v_options_1957_);
lean_inc(v_fileMap_1956_);
lean_inc(v_fileName_1955_);
lean_dec(v___y_1952_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_ref_1974_; lean_object* v___x_1976_; 
v_ref_1974_ = l_Lean_replaceRef(v_ref_1948_, v_ref_1960_);
lean_dec(v_ref_1960_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 5, v_ref_1974_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_fileName_1955_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_fileMap_1956_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_options_1957_);
lean_ctor_set(v_reuseFailAlloc_1978_, 3, v_currRecDepth_1958_);
lean_ctor_set(v_reuseFailAlloc_1978_, 4, v_maxRecDepth_1959_);
lean_ctor_set(v_reuseFailAlloc_1978_, 5, v_ref_1974_);
lean_ctor_set(v_reuseFailAlloc_1978_, 6, v_currNamespace_1961_);
lean_ctor_set(v_reuseFailAlloc_1978_, 7, v_openDecls_1962_);
lean_ctor_set(v_reuseFailAlloc_1978_, 8, v_initHeartbeats_1963_);
lean_ctor_set(v_reuseFailAlloc_1978_, 9, v_maxHeartbeats_1964_);
lean_ctor_set(v_reuseFailAlloc_1978_, 10, v_quotContext_1965_);
lean_ctor_set(v_reuseFailAlloc_1978_, 11, v_currMacroScope_1966_);
lean_ctor_set(v_reuseFailAlloc_1978_, 12, v_cancelTk_x3f_1968_);
lean_ctor_set(v_reuseFailAlloc_1978_, 13, v_inheritedTraceOptions_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*14, v_diag_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*14 + 1, v_suppressElabErrors_1969_);
v___x_1976_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1949_, v___y_1950_, v___y_1951_, v___x_1976_, v___y_1953_);
lean_dec_ref(v___x_1976_);
return v___x_1977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1980_, lean_object* v_msg_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_1980_, v_msg_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v_ref_1980_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_1988_, lean_object* v_msg_1989_, lean_object* v_declHint_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; lean_object* v_a_1997_; lean_object* v___x_1998_; 
v___x_1996_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_1989_, v_declHint_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref(v___x_1996_);
v___x_1998_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_1988_, v_a_1997_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_1999_, lean_object* v_msg_2000_, lean_object* v_declHint_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1999_, v_msg_2000_, v_declHint_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v_ref_1999_);
return v_res_2007_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2011_, lean_object* v_constName_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2018_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2019_ = 0;
lean_inc(v_constName_2012_);
v___x_2020_ = l_Lean_MessageData_ofConstName(v_constName_2012_, v___x_2019_);
v___x_2021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2018_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1);
v___x_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2011_, v___x_2023_, v_constName_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2025_, lean_object* v_constName_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_2025_, v_constName_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v_ref_2025_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(lean_object* v_constName_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_ref_2039_; lean_object* v___x_2040_; 
v_ref_2039_ = lean_ctor_get(v___y_2036_, 5);
lean_inc(v_ref_2039_);
v___x_2040_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_2039_, v_constName_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v_ref_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(lean_object* v_constName_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; lean_object* v_env_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2054_ = lean_st_ref_get(v___y_2052_);
v_env_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc_ref(v_env_2055_);
lean_dec(v___x_2054_);
v___x_2056_ = 0;
lean_inc(v_constName_2048_);
v___x_2057_ = l_Lean_Environment_findConstVal_x3f(v_env_2055_, v_constName_2048_, v___x_2056_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
return v___x_2058_;
}
else
{
lean_object* v_val_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v___y_2051_);
lean_dec(v_constName_2048_);
v_val_2059_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2057_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_val_2059_);
lean_dec(v___x_2057_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set_tag(v___x_2061_, 0);
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_val_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0___boxed(lean_object* v_constName_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(v_constName_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
return v_res_2073_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofForDecl___closed__1(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = ((lean_object*)(l_Lean_Meta_Grind_getProofForDecl___closed__0));
v___x_2076_ = l_Lean_stringToMessageData(v___x_2075_);
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofForDecl___closed__3(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = ((lean_object*)(l_Lean_Meta_Grind_getProofForDecl___closed__2));
v___x_2079_ = l_Lean_stringToMessageData(v___x_2078_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofForDecl(lean_object* v_declName_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v___x_2086_; 
lean_inc_ref(v_a_2083_);
lean_inc(v_declName_2080_);
v___x_2086_ = l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(v_declName_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2129_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2129_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2129_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2099_; lean_object* v_env_2100_; uint8_t v___x_2101_; 
v___x_2099_ = lean_st_ref_get(v_a_2084_);
v_env_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc_ref(v_env_2100_);
lean_dec(v___x_2099_);
lean_inc(v_declName_2080_);
v___x_2101_ = l_Lean_wasOriginallyTheorem(v_env_2100_, v_declName_2080_);
if (v___x_2101_ == 0)
{
lean_object* v_type_2102_; lean_object* v___x_2103_; 
v_type_2102_ = lean_ctor_get(v_a_2087_, 2);
lean_inc(v_a_2084_);
lean_inc_ref(v_a_2083_);
lean_inc(v_a_2082_);
lean_inc_ref(v_a_2081_);
lean_inc_ref(v_type_2102_);
v___x_2103_ = l_Lean_Meta_isProp(v_type_2102_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; uint8_t v___x_2105_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v___x_2103_);
v___x_2105_ = lean_unbox(v_a_2104_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_del_object(v___x_2089_);
lean_dec(v_a_2087_);
v___x_2106_ = lean_obj_once(&l_Lean_Meta_Grind_getProofForDecl___closed__1, &l_Lean_Meta_Grind_getProofForDecl___closed__1_once, _init_l_Lean_Meta_Grind_getProofForDecl___closed__1);
v___x_2107_ = lean_unbox(v_a_2104_);
lean_dec(v_a_2104_);
v___x_2108_ = l_Lean_MessageData_ofConstName(v_declName_2080_, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2106_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_obj_once(&l_Lean_Meta_Grind_getProofForDecl___closed__3, &l_Lean_Meta_Grind_getProofForDecl___closed__3_once, _init_l_Lean_Meta_Grind_getProofForDecl___closed__3);
v___x_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2109_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v___x_2111_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
else
{
lean_dec(v_a_2104_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
goto v___jp_2091_;
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_del_object(v___x_2089_);
lean_dec(v_a_2087_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_declName_2080_);
v_a_2121_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2103_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2103_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
goto v___jp_2091_;
}
v___jp_2091_:
{
lean_object* v_levelParams_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v_levelParams_2092_ = lean_ctor_get(v_a_2087_, 1);
lean_inc(v_levelParams_2092_);
lean_dec(v_a_2087_);
v___x_2093_ = lean_box(0);
v___x_2094_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(v_levelParams_2092_, v___x_2093_);
v___x_2095_ = l_Lean_mkConst(v_declName_2080_, v___x_2094_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2095_);
v___x_2097_ = v___x_2089_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
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
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_declName_2080_);
v_a_2130_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2086_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2086_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofForDecl___boxed(lean_object* v_declName_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Meta_Grind_getProofForDecl(v_declName_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(lean_object* v_00_u03b1_2145_, lean_object* v_constName_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2153_, lean_object* v_constName_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(v_00_u03b1_2153_, v_constName_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2161_, lean_object* v_ref_2162_, lean_object* v_constName_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_2162_, v_constName_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2170_, lean_object* v_ref_2171_, lean_object* v_constName_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(v_00_u03b1_2170_, v_ref_2171_, v_constName_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v_ref_2171_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2179_, lean_object* v_ref_2180_, lean_object* v_msg_2181_, lean_object* v_declHint_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2180_, v_msg_2181_, v_declHint_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2189_, lean_object* v_ref_2190_, lean_object* v_msg_2191_, lean_object* v_declHint_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2189_, v_ref_2190_, v_msg_2191_, v_declHint_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v_ref_2190_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2199_, lean_object* v_declHint_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2199_, v_declHint_2200_, v___y_2204_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2207_, lean_object* v_declHint_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2207_, v_declHint_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2215_, lean_object* v_ref_2216_, lean_object* v_msg_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2216_, v_msg_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2224_, lean_object* v_ref_2225_, lean_object* v_msg_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2224_, v_ref_2225_, v_msg_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v_ref_2225_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(lean_object* v___x_2233_, lean_object* v_s_2234_, lean_object* v_sym_2235_, lean_object* v___x_2236_, lean_object* v___x_2237_, lean_object* v_next_2238_, lean_object* v_acc_2239_, lean_object* v_h_2240_, lean_object* v_G_2241_){
_start:
{
uint8_t v___x_2242_; 
v___x_2242_ = lean_nat_dec_lt(v_next_2238_, v___x_2233_);
if (v___x_2242_ == 0)
{
lean_dec_ref(v_G_2241_);
lean_dec_ref(v___x_2237_);
lean_dec(v_sym_2235_);
lean_dec_ref(v_s_2234_);
lean_inc_ref(v_acc_2239_);
return v_acc_2239_;
}
else
{
lean_object* v___x_2243_; lean_object* v_smap_2244_; lean_object* v_origins_2245_; lean_object* v_erased_2246_; lean_object* v_omap_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2273_; 
v___x_2243_ = lean_array_fget(v_s_2234_, v_next_2238_);
v_smap_2244_ = lean_ctor_get(v___x_2243_, 0);
v_origins_2245_ = lean_ctor_get(v___x_2243_, 1);
v_erased_2246_ = lean_ctor_get(v___x_2243_, 2);
v_omap_2247_ = lean_ctor_get(v___x_2243_, 3);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2249_ = v___x_2243_;
v_isShared_2250_ = v_isSharedCheck_2273_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_omap_2247_);
lean_inc(v_erased_2246_);
lean_inc(v_origins_2245_);
lean_inc(v_smap_2244_);
lean_dec(v___x_2243_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2273_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_2252_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_2235_);
lean_inc_ref(v_smap_2244_);
v___x_2253_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_2251_, v___x_2252_, v_smap_2244_, v_sym_2235_);
if (lean_obj_tag(v___x_2253_) == 1)
{
lean_object* v_val_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2269_; 
lean_dec_ref(v_G_2241_);
lean_dec_ref(v___x_2237_);
v_val_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2269_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_val_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2269_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2258_ = l_Lean_PersistentHashMap_erase___redArg(v___x_2251_, v___x_2252_, v_smap_2244_, v_sym_2235_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2258_);
v___x_2260_ = v___x_2249_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_origins_2245_);
lean_ctor_set(v_reuseFailAlloc_2268_, 2, v_erased_2246_);
lean_ctor_set(v_reuseFailAlloc_2268_, 3, v_omap_2247_);
v___x_2260_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2261_ = lean_array_fset(v_s_2234_, v_next_2238_, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v_val_2254_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2262_);
v___x_2264_ = v___x_2256_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
lean_ctor_set(v___x_2266_, 1, v___x_2236_);
return v___x_2266_;
}
}
}
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec(v___x_2253_);
lean_del_object(v___x_2249_);
lean_dec_ref(v_omap_2247_);
lean_dec_ref(v_erased_2246_);
lean_dec_ref(v_origins_2245_);
lean_dec_ref(v_smap_2244_);
lean_dec(v_sym_2235_);
lean_dec_ref(v_s_2234_);
v___x_2270_ = lean_unsigned_to_nat(1u);
v___x_2271_ = lean_nat_add(v_next_2238_, v___x_2270_);
v___x_2272_ = lean_apply_4(v_G_2241_, v___x_2271_, v___x_2237_, lean_box(0), lean_box(0));
return v___x_2272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed(lean_object* v___x_2274_, lean_object* v_s_2275_, lean_object* v_sym_2276_, lean_object* v___x_2277_, lean_object* v___x_2278_, lean_object* v_next_2279_, lean_object* v_acc_2280_, lean_object* v_h_2281_, lean_object* v_G_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(v___x_2274_, v_s_2275_, v_sym_2276_, v___x_2277_, v___x_2278_, v_next_2279_, v_acc_2280_, v_h_2281_, v_G_2282_);
lean_dec_ref(v_acc_2280_);
lean_dec(v_next_2279_);
lean_dec(v___x_2274_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(lean_object* v_s_2287_, lean_object* v_sym_2288_){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___f_2294_; lean_object* v___x_2295_; lean_object* v_fst_2296_; 
v___x_2289_ = lean_array_get_size(v_s_2287_);
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = lean_box(0);
v___x_2292_ = lean_box(0);
v___x_2293_ = ((lean_object*)(l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___closed__0));
v___f_2294_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed), 9, 5);
lean_closure_set(v___f_2294_, 0, v___x_2289_);
lean_closure_set(v___f_2294_, 1, v_s_2287_);
lean_closure_set(v___f_2294_, 2, v_sym_2288_);
lean_closure_set(v___f_2294_, 3, v___x_2292_);
lean_closure_set(v___f_2294_, 4, v___x_2293_);
v___x_2295_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2294_, v___x_2290_, v___x_2293_, lean_box(0));
v_fst_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_fst_2296_);
lean_dec(v___x_2295_);
if (lean_obj_tag(v_fst_2296_) == 0)
{
return v___x_2291_;
}
else
{
lean_object* v_val_2297_; 
v_val_2297_ = lean_ctor_get(v_fst_2296_, 0);
lean_inc(v_val_2297_);
lean_dec_ref(v_fst_2296_);
return v_val_2297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f(lean_object* v_00_u03b1_2298_, lean_object* v_s_2299_, lean_object* v_sym_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(v_s_2299_, v_sym_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0(void){
_start:
{
lean_object* v___f_2302_; lean_object* v___f_2303_; lean_object* v___x_2304_; 
v___f_2302_ = ((lean_object*)(l_Lean_Meta_Grind_instHashableOrigin___closed__0));
v___f_2303_ = ((lean_object*)(l_Lean_Meta_Grind_instBEqOrigin___closed__0));
v___x_2304_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___f_2303_, v___f_2302_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v_thms_2307_; 
v___x_2305_ = lean_obj_once(&l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0, &l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0_once, _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0);
v___x_2306_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1);
v_thms_2307_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_thms_2307_, 0, v___x_2306_);
lean_ctor_set(v_thms_2307_, 1, v___x_2305_);
lean_ctor_set(v_thms_2307_, 2, v___x_2305_);
lean_ctor_set(v_thms_2307_, 3, v___x_2306_);
return v_thms_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert___redArg(lean_object* v_inst_2308_, lean_object* v_s_2309_, lean_object* v_thm_2310_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2311_ = lean_array_get_size(v_s_2309_);
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_nat_dec_eq(v___x_2311_, v___x_2312_);
if (v___x_2313_ == 0)
{
uint8_t v___x_2314_; 
v___x_2314_ = lean_nat_dec_lt(v___x_2312_, v___x_2311_);
if (v___x_2314_ == 0)
{
lean_dec(v_thm_2310_);
lean_dec_ref(v_inst_2308_);
return v_s_2309_;
}
else
{
lean_object* v_v_2315_; lean_object* v___x_2316_; lean_object* v_xs_x27_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_v_2315_ = lean_array_fget(v_s_2309_, v___x_2312_);
v___x_2316_ = lean_box(0);
v_xs_x27_2317_ = lean_array_fset(v_s_2309_, v___x_2312_, v___x_2316_);
v___x_2318_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_2308_, v_v_2315_, v_thm_2310_);
v___x_2319_ = lean_array_fset(v_xs_x27_2317_, v___x_2312_, v___x_2318_);
return v___x_2319_;
}
}
else
{
lean_object* v_thms_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_dec_ref(v_s_2309_);
v_thms_2320_ = lean_obj_once(&l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1, &l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1_once, _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1);
v___x_2321_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_2308_, v_thms_2320_, v_thm_2310_);
v___x_2322_ = lean_unsigned_to_nat(1u);
v___x_2323_ = lean_mk_empty_array_with_capacity(v___x_2322_);
v___x_2324_ = lean_array_push(v___x_2323_, v___x_2321_);
return v___x_2324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert(lean_object* v_00_u03b1_2325_, lean_object* v_inst_2326_, lean_object* v_s_2327_, lean_object* v_thm_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Meta_Grind_TheoremsArray_insert___redArg(v_inst_2326_, v_s_2327_, v_thm_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(lean_object* v_origin_2330_, lean_object* v_as_2331_, size_t v_i_2332_, size_t v_stop_2333_){
_start:
{
uint8_t v___x_2334_; 
v___x_2334_ = lean_usize_dec_eq(v_i_2332_, v_stop_2333_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v_erased_2336_; uint8_t v___x_2337_; 
v___x_2335_ = lean_array_uget_borrowed(v_as_2331_, v_i_2332_);
v_erased_2336_ = lean_ctor_get(v___x_2335_, 2);
lean_inc_ref(v_erased_2336_);
v___x_2337_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_erased_2336_, v_origin_2330_);
if (v___x_2337_ == 0)
{
size_t v___x_2338_; size_t v___x_2339_; 
v___x_2338_ = ((size_t)1ULL);
v___x_2339_ = lean_usize_add(v_i_2332_, v___x_2338_);
v_i_2332_ = v___x_2339_;
goto _start;
}
else
{
return v___x_2337_;
}
}
else
{
uint8_t v___x_2341_; 
v___x_2341_ = 0;
return v___x_2341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg___boxed(lean_object* v_origin_2342_, lean_object* v_as_2343_, lean_object* v_i_2344_, lean_object* v_stop_2345_){
_start:
{
size_t v_i_boxed_2346_; size_t v_stop_boxed_2347_; uint8_t v_res_2348_; lean_object* v_r_2349_; 
v_i_boxed_2346_ = lean_unbox_usize(v_i_2344_);
lean_dec(v_i_2344_);
v_stop_boxed_2347_ = lean_unbox_usize(v_stop_2345_);
lean_dec(v_stop_2345_);
v_res_2348_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2342_, v_as_2343_, v_i_boxed_2346_, v_stop_boxed_2347_);
lean_dec_ref(v_as_2343_);
lean_dec_ref(v_origin_2342_);
v_r_2349_ = lean_box(v_res_2348_);
return v_r_2349_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(lean_object* v_s_2350_, lean_object* v_origin_2351_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2352_ = lean_unsigned_to_nat(0u);
v___x_2353_ = lean_array_get_size(v_s_2350_);
v___x_2354_ = lean_nat_dec_lt(v___x_2352_, v___x_2353_);
if (v___x_2354_ == 0)
{
return v___x_2354_;
}
else
{
if (v___x_2354_ == 0)
{
return v___x_2354_;
}
else
{
size_t v___x_2355_; size_t v___x_2356_; uint8_t v___x_2357_; 
v___x_2355_ = ((size_t)0ULL);
v___x_2356_ = lean_usize_of_nat(v___x_2353_);
v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2351_, v_s_2350_, v___x_2355_, v___x_2356_);
return v___x_2357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___redArg___boxed(lean_object* v_s_2358_, lean_object* v_origin_2359_){
_start:
{
uint8_t v_res_2360_; lean_object* v_r_2361_; 
v_res_2360_ = l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(v_s_2358_, v_origin_2359_);
lean_dec_ref(v_origin_2359_);
lean_dec_ref(v_s_2358_);
v_r_2361_ = lean_box(v_res_2360_);
return v_r_2361_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased(lean_object* v_00_u03b1_2362_, lean_object* v_s_2363_, lean_object* v_origin_2364_){
_start:
{
uint8_t v___x_2365_; 
v___x_2365_ = l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(v_s_2363_, v_origin_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___boxed(lean_object* v_00_u03b1_2366_, lean_object* v_s_2367_, lean_object* v_origin_2368_){
_start:
{
uint8_t v_res_2369_; lean_object* v_r_2370_; 
v_res_2369_ = l_Lean_Meta_Grind_TheoremsArray_isErased(v_00_u03b1_2366_, v_s_2367_, v_origin_2368_);
lean_dec_ref(v_origin_2368_);
lean_dec_ref(v_s_2367_);
v_r_2370_ = lean_box(v_res_2369_);
return v_r_2370_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(lean_object* v_00_u03b1_2371_, lean_object* v_origin_2372_, lean_object* v_as_2373_, size_t v_i_2374_, size_t v_stop_2375_){
_start:
{
uint8_t v___x_2376_; 
v___x_2376_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2372_, v_as_2373_, v_i_2374_, v_stop_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___boxed(lean_object* v_00_u03b1_2377_, lean_object* v_origin_2378_, lean_object* v_as_2379_, lean_object* v_i_2380_, lean_object* v_stop_2381_){
_start:
{
size_t v_i_boxed_2382_; size_t v_stop_boxed_2383_; uint8_t v_res_2384_; lean_object* v_r_2385_; 
v_i_boxed_2382_ = lean_unbox_usize(v_i_2380_);
lean_dec(v_i_2380_);
v_stop_boxed_2383_ = lean_unbox_usize(v_stop_2381_);
lean_dec(v_stop_2381_);
v_res_2384_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(v_00_u03b1_2377_, v_origin_2378_, v_as_2379_, v_i_boxed_2382_, v_stop_boxed_2383_);
lean_dec_ref(v_as_2379_);
lean_dec_ref(v_origin_2378_);
v_r_2385_ = lean_box(v_res_2384_);
return v_r_2385_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(lean_object* v_upperBound_2386_, lean_object* v_s_2387_, lean_object* v_origin_2388_, lean_object* v_a_2389_, lean_object* v_b_2390_){
_start:
{
lean_object* v_a_2392_; uint8_t v___x_2396_; 
v___x_2396_ = lean_nat_dec_lt(v_a_2389_, v_upperBound_2386_);
if (v___x_2396_ == 0)
{
lean_dec(v_a_2389_);
return v_b_2390_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2397_ = lean_array_fget_borrowed(v_s_2387_, v_a_2389_);
lean_inc(v___x_2397_);
v___x_2398_ = l_Lean_Meta_Grind_Theorems_find___redArg(v___x_2397_, v_origin_2388_);
v___x_2399_ = l_List_isEmpty___redArg(v___x_2398_);
if (v___x_2399_ == 0)
{
lean_object* v___x_2400_; 
v___x_2400_ = l_List_appendTR___redArg(v_b_2390_, v___x_2398_);
v_a_2392_ = v___x_2400_;
goto v___jp_2391_;
}
else
{
lean_dec(v___x_2398_);
v_a_2392_ = v_b_2390_;
goto v___jp_2391_;
}
}
v___jp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_unsigned_to_nat(1u);
v___x_2394_ = lean_nat_add(v_a_2389_, v___x_2393_);
lean_dec(v_a_2389_);
v_a_2389_ = v___x_2394_;
v_b_2390_ = v_a_2392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg___boxed(lean_object* v_upperBound_2401_, lean_object* v_s_2402_, lean_object* v_origin_2403_, lean_object* v_a_2404_, lean_object* v_b_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v_upperBound_2401_, v_s_2402_, v_origin_2403_, v_a_2404_, v_b_2405_);
lean_dec_ref(v_origin_2403_);
lean_dec_ref(v_s_2402_);
lean_dec(v_upperBound_2401_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg(lean_object* v_s_2407_, lean_object* v_origin_2408_){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v_r_2411_; lean_object* v___x_2412_; 
v___x_2409_ = lean_array_get_size(v_s_2407_);
v___x_2410_ = lean_unsigned_to_nat(0u);
v_r_2411_ = lean_box(0);
v___x_2412_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v___x_2409_, v_s_2407_, v_origin_2408_, v___x_2410_, v_r_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg___boxed(lean_object* v_s_2413_, lean_object* v_origin_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_Meta_Grind_TheoremsArray_find___redArg(v_s_2413_, v_origin_2414_);
lean_dec_ref(v_origin_2414_);
lean_dec_ref(v_s_2413_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find(lean_object* v_00_u03b1_2416_, lean_object* v_s_2417_, lean_object* v_origin_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_Meta_Grind_TheoremsArray_find___redArg(v_s_2417_, v_origin_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___boxed(lean_object* v_00_u03b1_2420_, lean_object* v_s_2421_, lean_object* v_origin_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Meta_Grind_TheoremsArray_find(v_00_u03b1_2420_, v_s_2421_, v_origin_2422_);
lean_dec_ref(v_origin_2422_);
lean_dec_ref(v_s_2421_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(lean_object* v_00_u03b1_2424_, lean_object* v_upperBound_2425_, lean_object* v_s_2426_, lean_object* v_origin_2427_, lean_object* v_inst_2428_, lean_object* v_R_2429_, lean_object* v_a_2430_, lean_object* v_b_2431_, lean_object* v_c_2432_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v_upperBound_2425_, v_s_2426_, v_origin_2427_, v_a_2430_, v_b_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_upperBound_2435_, lean_object* v_s_2436_, lean_object* v_origin_2437_, lean_object* v_inst_2438_, lean_object* v_R_2439_, lean_object* v_a_2440_, lean_object* v_b_2441_, lean_object* v_c_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(v_00_u03b1_2434_, v_upperBound_2435_, v_s_2436_, v_origin_2437_, v_inst_2438_, v_R_2439_, v_a_2440_, v_b_2441_, v_c_2442_);
lean_dec_ref(v_origin_2437_);
lean_dec_ref(v_s_2436_);
lean_dec(v_upperBound_2435_);
return v_res_2443_;
}
}
lean_object* runtime_initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eqns(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Theorems(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Theorems(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Theorems(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
}
#ifdef __cplusplus
}
#endif
