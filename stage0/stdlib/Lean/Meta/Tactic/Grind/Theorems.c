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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15_value;
static const lean_closure_object l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17;
static lean_once_cell_t l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_t_8_, 2);
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
lean_dec_ref_known(v_x_91_, 1);
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
lean_inc(v___y_95_);
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
lean_dec_ref_known(v_x_91_, 1);
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
lean_inc(v___y_110_);
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
lean_inc(v___y_129_);
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
lean_dec_ref_known(v_x_91_, 1);
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
lean_inc(v___y_151_);
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
lean_dec_ref_known(v_o_173_, 1);
v___x_175_ = 0;
v___x_176_ = l_Lean_MessageData_ofConstName(v_declName_174_, v___x_175_);
return v___x_176_;
}
case 1:
{
lean_object* v_fvarId_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_fvarId_177_ = lean_ctor_get(v_o_173_, 0);
lean_inc(v_fvarId_177_);
lean_dec_ref_known(v_o_173_, 1);
v___x_178_ = l_Lean_mkFVar(v_fvarId_177_);
v___x_179_ = l_Lean_MessageData_ofExpr(v___x_178_);
return v___x_179_;
}
case 2:
{
lean_object* v_ref_180_; lean_object* v___x_181_; 
v_ref_180_ = lean_ctor_get(v_o_173_, 1);
lean_inc(v_ref_180_);
lean_dec_ref_known(v_o_173_, 2);
v___x_181_ = l_Lean_MessageData_ofSyntax(v_ref_180_);
return v___x_181_;
}
default: 
{
lean_object* v_id_182_; lean_object* v___x_183_; 
v_id_182_ = lean_ctor_get(v_o_173_, 0);
lean_inc(v_id_182_);
lean_dec_ref_known(v_o_173_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_object* v_00_u03b1_222_){
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
lean_dec_ref_known(v_head_271_, 1);
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
lean_inc_ref_n(v_origin_289_, 2);
v_origins_291_ = l_Lean_PersistentHashMap_insert___redArg(v___f_284_, v___f_285_, v_origins_278_, v_origin_289_, v___x_290_);
v_erased_292_ = l_Lean_PersistentHashMap_erase___redArg(v___f_284_, v___f_285_, v_erased_279_, v_origin_289_);
lean_inc(v_constName_276_);
v___x_312_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_286_, v___x_287_, v_smap_277_, v_constName_276_);
if (lean_obj_tag(v___x_312_) == 1)
{
lean_object* v_val_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_val_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_313_);
lean_dec_ref_known(v___x_312_, 1);
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
v___x_295_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_284_, v___f_285_, v_omap_280_, v_origin_289_);
if (lean_obj_tag(v___x_295_) == 1)
{
lean_object* v_val_296_; lean_object* v___x_298_; 
v_val_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_val_296_);
lean_dec_ref_known(v___x_295_, 1);
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
lean_dec_ref_known(v___x_270_, 2);
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
v___y_331_ = v___y_341_;
v___y_332_ = v_declName_342_;
goto v___jp_330_;
}
}
v___jp_330_:
{
uint8_t v___x_333_; 
v___x_333_ = lean_name_eq(v___y_331_, v___y_332_);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(lean_object* v_x_349_, size_t v_x_350_, lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
lean_object* v_es_352_; lean_object* v___x_353_; size_t v___x_354_; size_t v___x_355_; lean_object* v_j_356_; lean_object* v___x_357_; 
v_es_352_ = lean_ctor_get(v_x_349_, 0);
v___x_353_ = lean_box(2);
v___x_354_ = ((size_t)31ULL);
v___x_355_ = lean_usize_land(v_x_350_, v___x_354_);
v_j_356_ = lean_usize_to_nat(v___x_355_);
v___x_357_ = lean_array_get_borrowed(v___x_353_, v_es_352_, v_j_356_);
lean_dec(v_j_356_);
switch(lean_obj_tag(v___x_357_))
{
case 0:
{
lean_object* v_key_358_; lean_object* v___y_360_; lean_object* v_declName_363_; 
v_key_358_ = lean_ctor_get(v___x_357_, 0);
v_declName_363_ = lean_ctor_get(v_x_351_, 0);
v___y_360_ = v_declName_363_;
goto v___jp_359_;
v___jp_359_:
{
lean_object* v_declName_361_; uint8_t v___x_362_; 
v_declName_361_ = lean_ctor_get(v_key_358_, 0);
v___x_362_ = lean_name_eq(v___y_360_, v_declName_361_);
return v___x_362_;
}
}
case 1:
{
lean_object* v_node_364_; size_t v___x_365_; size_t v___x_366_; 
v_node_364_ = lean_ctor_get(v___x_357_, 0);
v___x_365_ = ((size_t)5ULL);
v___x_366_ = lean_usize_shift_right(v_x_350_, v___x_365_);
v_x_349_ = v_node_364_;
v_x_350_ = v___x_366_;
goto _start;
}
default: 
{
uint8_t v___x_368_; 
v___x_368_ = 0;
return v___x_368_;
}
}
}
else
{
lean_object* v_ks_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_ks_369_ = lean_ctor_get(v_x_349_, 0);
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_ks_369_, v___x_370_, v_x_351_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
size_t v_x_204__boxed_375_; uint8_t v_res_376_; lean_object* v_r_377_; 
v_x_204__boxed_375_ = lean_unbox_usize(v_x_373_);
lean_dec(v_x_373_);
v_res_376_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_372_, v_x_204__boxed_375_, v_x_374_);
lean_dec_ref(v_x_374_);
lean_dec_ref(v_x_372_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
uint64_t v___y_381_; lean_object* v___y_385_; lean_object* v_declName_388_; 
v_declName_388_ = lean_ctor_get(v_x_379_, 0);
v___y_385_ = v_declName_388_;
goto v___jp_384_;
v___jp_380_:
{
size_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_uint64_to_usize(v___y_381_);
v___x_383_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_378_, v___x_382_, v_x_379_);
return v___x_383_;
}
v___jp_384_:
{
if (lean_obj_tag(v___y_385_) == 0)
{
uint64_t v___x_386_; 
v___x_386_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0, &l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0);
v___y_381_ = v___x_386_;
goto v___jp_380_;
}
else
{
uint64_t v_hash_387_; 
v_hash_387_ = lean_ctor_get_uint64(v___y_385_, sizeof(void*)*2);
v___y_381_ = v_hash_387_;
goto v___jp_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg___boxed(lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_x_389_, v_x_390_);
lean_dec_ref(v_x_390_);
lean_dec_ref(v_x_389_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object* v_s_393_, lean_object* v_origin_394_){
_start:
{
lean_object* v_origins_395_; uint8_t v___x_396_; 
v_origins_395_ = lean_ctor_get(v_s_393_, 1);
v___x_396_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_origins_395_, v_origin_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___redArg___boxed(lean_object* v_s_397_, lean_object* v_origin_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_397_, v_origin_398_);
lean_dec_ref(v_origin_398_);
lean_dec_ref(v_s_397_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_contains(lean_object* v_00_u03b1_401_, lean_object* v_s_402_, lean_object* v_origin_403_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_402_, v_origin_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_contains___boxed(lean_object* v_00_u03b1_405_, lean_object* v_s_406_, lean_object* v_origin_407_){
_start:
{
uint8_t v_res_408_; lean_object* v_r_409_; 
v_res_408_ = l_Lean_Meta_Grind_Theorems_contains(v_00_u03b1_405_, v_s_406_, v_origin_407_);
lean_dec_ref(v_origin_407_);
lean_dec_ref(v_s_406_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(lean_object* v_00_u03b2_410_, lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
uint8_t v___x_413_; 
v___x_413_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_x_411_, v_x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___boxed(lean_object* v_00_u03b2_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0(v_00_u03b2_414_, v_x_415_, v_x_416_);
lean_dec_ref(v_x_416_);
lean_dec_ref(v_x_415_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(lean_object* v_00_u03b2_419_, lean_object* v_x_420_, size_t v_x_421_, lean_object* v_x_422_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___redArg(v_x_420_, v_x_421_, v_x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
size_t v_x_305__boxed_428_; uint8_t v_res_429_; lean_object* v_r_430_; 
v_x_305__boxed_428_ = lean_unbox_usize(v_x_426_);
lean_dec(v_x_426_);
v_res_429_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0(v_00_u03b2_424_, v_x_425_, v_x_305__boxed_428_, v_x_427_);
lean_dec_ref(v_x_427_);
lean_dec_ref(v_x_425_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_431_, lean_object* v_keys_432_, lean_object* v_vals_433_, lean_object* v_heq_434_, lean_object* v_i_435_, lean_object* v_k_436_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___redArg(v_keys_432_, v_i_435_, v_k_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_438_, lean_object* v_keys_439_, lean_object* v_vals_440_, lean_object* v_heq_441_, lean_object* v_i_442_, lean_object* v_k_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0_spec__0_spec__1(v_00_u03b2_438_, v_keys_439_, v_vals_440_, v_heq_441_, v_i_442_, v_k_443_);
lean_dec_ref(v_k_443_);
lean_dec_ref(v_vals_440_);
lean_dec_ref(v_keys_439_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(lean_object* v_xs_446_, lean_object* v_v_447_, lean_object* v_i_448_){
_start:
{
lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_458_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_array_get_size(v_xs_446_);
v___x_461_ = lean_nat_dec_lt(v_i_448_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_dec(v_i_448_);
v___x_462_ = lean_box(0);
return v___x_462_;
}
else
{
lean_object* v___x_463_; lean_object* v_declName_464_; 
v___x_463_ = lean_array_fget_borrowed(v_xs_446_, v_i_448_);
v_declName_464_ = lean_ctor_get(v___x_463_, 0);
v___y_458_ = v_declName_464_;
goto v___jp_457_;
}
v___jp_449_:
{
uint8_t v___x_452_; 
v___x_452_ = lean_name_eq(v___y_450_, v___y_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_nat_add(v_i_448_, v___x_453_);
lean_dec(v_i_448_);
v_i_448_ = v___x_454_;
goto _start;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v_i_448_);
return v___x_456_;
}
}
v___jp_457_:
{
lean_object* v_declName_459_; 
v_declName_459_ = lean_ctor_get(v_v_447_, 0);
v___y_450_ = v___y_458_;
v___y_451_ = v_declName_459_;
goto v___jp_449_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_xs_465_, lean_object* v_v_466_, lean_object* v_i_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(v_xs_465_, v_v_466_, v_i_467_);
lean_dec_ref(v_v_466_);
lean_dec_ref(v_xs_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(lean_object* v_xs_469_, lean_object* v_v_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1_spec__3(v_xs_469_, v_v_470_, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_473_, lean_object* v_v_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(v_xs_473_, v_v_474_);
lean_dec_ref(v_v_474_);
lean_dec_ref(v_xs_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(lean_object* v_x_476_, size_t v_x_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v_es_479_; lean_object* v___x_480_; size_t v___x_481_; size_t v___x_482_; lean_object* v_j_483_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v_entry_497_; 
v_es_479_ = lean_ctor_get(v_x_476_, 0);
v___x_480_ = lean_box(2);
v___x_481_ = ((size_t)31ULL);
v___x_482_ = lean_usize_land(v_x_477_, v___x_481_);
v_j_483_ = lean_usize_to_nat(v___x_482_);
v_entry_497_ = lean_array_get(v___x_480_, v_es_479_, v_j_483_);
switch(lean_obj_tag(v_entry_497_))
{
case 0:
{
lean_object* v_key_498_; lean_object* v___y_500_; lean_object* v_declName_502_; 
v_key_498_ = lean_ctor_get(v_entry_497_, 0);
lean_inc(v_key_498_);
lean_dec_ref_known(v_entry_497_, 2);
v_declName_502_ = lean_ctor_get(v_x_478_, 0);
v___y_500_ = v_declName_502_;
goto v___jp_499_;
v___jp_499_:
{
lean_object* v_declName_501_; 
v_declName_501_ = lean_ctor_get(v_key_498_, 0);
lean_inc(v_declName_501_);
lean_dec(v_key_498_);
v___y_485_ = v___y_500_;
v___y_486_ = v_declName_501_;
goto v___jp_484_;
}
}
case 1:
{
lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_537_; 
lean_inc_ref(v_es_479_);
v_isSharedCheck_537_ = !lean_is_exclusive(v_x_476_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; 
v_unused_538_ = lean_ctor_get(v_x_476_, 0);
lean_dec(v_unused_538_);
v___x_504_ = v_x_476_;
v_isShared_505_ = v_isSharedCheck_537_;
goto v_resetjp_503_;
}
else
{
lean_dec(v_x_476_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_537_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_node_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_536_; 
v_node_506_ = lean_ctor_get(v_entry_497_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_entry_497_);
if (v_isSharedCheck_536_ == 0)
{
v___x_508_ = v_entry_497_;
v_isShared_509_ = v_isSharedCheck_536_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_node_506_);
lean_dec(v_entry_497_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_536_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
size_t v___x_510_; lean_object* v_entries_511_; size_t v___x_512_; lean_object* v_newNode_513_; lean_object* v___x_514_; 
v___x_510_ = ((size_t)5ULL);
v_entries_511_ = lean_array_set(v_es_479_, v_j_483_, v___x_480_);
v___x_512_ = lean_usize_shift_right(v_x_477_, v___x_510_);
v_newNode_513_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_node_506_, v___x_512_, v_x_478_);
lean_inc_ref(v_newNode_513_);
v___x_514_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_513_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v___x_516_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v_newNode_513_);
v___x_516_ = v___x_508_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_newNode_513_);
v___x_516_ = v_reuseFailAlloc_521_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = lean_array_set(v_entries_511_, v_j_483_, v___x_516_);
lean_dec(v_j_483_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_517_);
v___x_519_ = v___x_504_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_object* v_val_522_; lean_object* v_fst_523_; lean_object* v_snd_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_535_; 
lean_dec_ref(v_newNode_513_);
lean_del_object(v___x_508_);
v_val_522_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_val_522_);
lean_dec_ref_known(v___x_514_, 1);
v_fst_523_ = lean_ctor_get(v_val_522_, 0);
v_snd_524_ = lean_ctor_get(v_val_522_, 1);
v_isSharedCheck_535_ = !lean_is_exclusive(v_val_522_);
if (v_isSharedCheck_535_ == 0)
{
v___x_526_ = v_val_522_;
v_isShared_527_ = v_isSharedCheck_535_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_snd_524_);
lean_inc(v_fst_523_);
lean_dec(v_val_522_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_535_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_fst_523_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_snd_524_);
v___x_529_ = v_reuseFailAlloc_534_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = lean_array_set(v_entries_511_, v_j_483_, v___x_529_);
lean_dec(v_j_483_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_530_);
v___x_532_ = v___x_504_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_483_);
return v_x_476_;
}
}
v___jp_484_:
{
uint8_t v___x_487_; 
v___x_487_ = lean_name_eq(v___y_485_, v___y_486_);
lean_dec(v___y_486_);
if (v___x_487_ == 0)
{
lean_dec(v_j_483_);
return v_x_476_;
}
else
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_495_; 
lean_inc_ref(v_es_479_);
v_isSharedCheck_495_ = !lean_is_exclusive(v_x_476_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v_x_476_, 0);
lean_dec(v_unused_496_);
v___x_489_ = v_x_476_;
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
else
{
lean_dec(v_x_476_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = lean_array_set(v_es_479_, v_j_483_, v___x_480_);
lean_dec(v_j_483_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_491_);
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
else
{
lean_object* v_ks_539_; lean_object* v_vs_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_554_; 
v_ks_539_ = lean_ctor_get(v_x_476_, 0);
v_vs_540_ = lean_ctor_get(v_x_476_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_x_476_);
if (v_isSharedCheck_554_ == 0)
{
v___x_542_ = v_x_476_;
v_isShared_543_ = v_isSharedCheck_554_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_vs_540_);
lean_inc(v_ks_539_);
lean_dec(v_x_476_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_554_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; 
v___x_544_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0_spec__1(v_ks_539_, v_x_478_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_546_; 
if (v_isShared_543_ == 0)
{
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_ks_539_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_vs_540_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
else
{
lean_object* v_val_548_; lean_object* v_keys_x27_549_; lean_object* v_vals_x27_550_; lean_object* v___x_552_; 
v_val_548_ = lean_ctor_get(v___x_544_, 0);
lean_inc_n(v_val_548_, 2);
lean_dec_ref_known(v___x_544_, 1);
v_keys_x27_549_ = l_Array_eraseIdx___redArg(v_ks_539_, v_val_548_);
v_vals_x27_550_ = l_Array_eraseIdx___redArg(v_vs_540_, v_val_548_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v_vals_x27_550_);
lean_ctor_set(v___x_542_, 0, v_keys_x27_549_);
v___x_552_ = v___x_542_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_keys_x27_549_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_vals_x27_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
size_t v_x_594__boxed_558_; lean_object* v_res_559_; 
v_x_594__boxed_558_ = lean_unbox_usize(v_x_556_);
lean_dec(v_x_556_);
v_res_559_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_555_, v_x_594__boxed_558_, v_x_557_);
lean_dec_ref(v_x_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
uint64_t v___y_563_; lean_object* v___y_567_; lean_object* v_declName_570_; 
v_declName_570_ = lean_ctor_get(v_x_561_, 0);
v___y_567_ = v_declName_570_;
goto v___jp_566_;
v___jp_562_:
{
size_t v_h_564_; lean_object* v___x_565_; 
v_h_564_ = lean_uint64_to_usize(v___y_563_);
v___x_565_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_560_, v_h_564_, v_x_561_);
return v___x_565_;
}
v___jp_566_:
{
if (lean_obj_tag(v___y_567_) == 0)
{
uint64_t v___x_568_; 
v___x_568_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0, &l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0);
v___y_563_ = v___x_568_;
goto v___jp_562_;
}
else
{
uint64_t v_hash_569_; 
v_hash_569_ = lean_ctor_get_uint64(v___y_567_, sizeof(void*)*2);
v___y_563_ = v_hash_569_;
goto v___jp_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg___boxed(lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_x_571_, v_x_572_);
lean_dec_ref(v_x_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
lean_object* v_ks_578_; lean_object* v_vs_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_608_; 
v_ks_578_ = lean_ctor_get(v_x_574_, 0);
v_vs_579_ = lean_ctor_get(v_x_574_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_x_574_);
if (v_isSharedCheck_608_ == 0)
{
v___x_581_ = v_x_574_;
v_isShared_582_ = v_isSharedCheck_608_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_vs_579_);
lean_inc(v_ks_578_);
lean_dec(v_x_574_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_608_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_array_get_size(v_ks_578_);
v___x_599_ = lean_nat_dec_lt(v_x_575_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_del_object(v___x_581_);
lean_dec(v_x_575_);
v___x_600_ = lean_array_push(v_ks_578_, v_x_576_);
v___x_601_ = lean_array_push(v_vs_579_, v_x_577_);
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
return v___x_602_;
}
else
{
lean_object* v_k_x27_603_; lean_object* v___y_605_; lean_object* v_declName_607_; 
v_k_x27_603_ = lean_array_fget_borrowed(v_ks_578_, v_x_575_);
v_declName_607_ = lean_ctor_get(v_x_576_, 0);
lean_inc(v_declName_607_);
v___y_605_ = v_declName_607_;
goto v___jp_604_;
v___jp_604_:
{
lean_object* v_declName_606_; 
v_declName_606_ = lean_ctor_get(v_k_x27_603_, 0);
lean_inc(v_declName_606_);
v___y_584_ = v___y_605_;
v___y_585_ = v_declName_606_;
goto v___jp_583_;
}
}
v___jp_583_:
{
uint8_t v___x_586_; 
v___x_586_ = lean_name_eq(v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec(v___y_584_);
if (v___x_586_ == 0)
{
lean_object* v___x_588_; 
if (v_isShared_582_ == 0)
{
v___x_588_ = v___x_581_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_ks_578_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_vs_579_);
v___x_588_ = v_reuseFailAlloc_592_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_add(v_x_575_, v___x_589_);
lean_dec(v_x_575_);
v_x_574_ = v___x_588_;
v_x_575_ = v___x_590_;
goto _start;
}
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_593_ = lean_array_fset(v_ks_578_, v_x_575_, v_x_576_);
v___x_594_ = lean_array_fset(v_vs_579_, v_x_575_, v_x_577_);
lean_dec(v_x_575_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v___x_594_);
lean_ctor_set(v___x_581_, 0, v___x_593_);
v___x_596_ = v___x_581_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(lean_object* v_n_609_, lean_object* v_k_610_, lean_object* v_v_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(v_n_609_, v___x_612_, v_k_610_, v_v_611_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(lean_object* v_x_615_, size_t v_x_616_, size_t v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
lean_object* v_es_620_; size_t v___x_621_; size_t v___x_622_; lean_object* v_j_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_es_620_ = lean_ctor_get(v_x_615_, 0);
v___x_621_ = ((size_t)31ULL);
v___x_622_ = lean_usize_land(v_x_616_, v___x_621_);
v_j_623_ = lean_usize_to_nat(v___x_622_);
v___x_624_ = lean_array_get_size(v_es_620_);
v___x_625_ = lean_nat_dec_lt(v_j_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_dec(v_j_623_);
lean_dec(v_x_619_);
lean_dec_ref(v_x_618_);
return v_x_615_;
}
else
{
lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_671_; 
lean_inc_ref(v_es_620_);
v_isSharedCheck_671_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v_x_615_, 0);
lean_dec(v_unused_672_);
v___x_627_ = v_x_615_;
v_isShared_628_ = v_isSharedCheck_671_;
goto v_resetjp_626_;
}
else
{
lean_dec(v_x_615_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_671_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_v_629_; lean_object* v___x_630_; lean_object* v_xs_x27_631_; lean_object* v___y_633_; 
v_v_629_ = lean_array_fget(v_es_620_, v_j_623_);
v___x_630_ = lean_box(0);
v_xs_x27_631_ = lean_array_fset(v_es_620_, v_j_623_, v___x_630_);
switch(lean_obj_tag(v_v_629_))
{
case 0:
{
lean_object* v_key_638_; lean_object* v_val_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_656_; 
v_key_638_ = lean_ctor_get(v_v_629_, 0);
v_val_639_ = lean_ctor_get(v_v_629_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_v_629_);
if (v_isSharedCheck_656_ == 0)
{
v___x_641_ = v_v_629_;
v_isShared_642_ = v_isSharedCheck_656_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_val_639_);
lean_inc(v_key_638_);
lean_dec(v_v_629_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_656_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_653_; lean_object* v_declName_655_; 
v_declName_655_ = lean_ctor_get(v_x_618_, 0);
lean_inc(v_declName_655_);
v___y_653_ = v_declName_655_;
goto v___jp_652_;
v___jp_643_:
{
uint8_t v___x_646_; 
v___x_646_ = lean_name_eq(v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec(v___y_644_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_del_object(v___x_641_);
v___x_647_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_638_, v_val_639_, v_x_618_, v_x_619_);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
v___y_633_ = v___x_648_;
goto v___jp_632_;
}
else
{
lean_object* v___x_650_; 
lean_dec(v_val_639_);
lean_dec(v_key_638_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_x_619_);
lean_ctor_set(v___x_641_, 0, v_x_618_);
v___x_650_ = v___x_641_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_x_618_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_x_619_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
v___y_633_ = v___x_650_;
goto v___jp_632_;
}
}
}
v___jp_652_:
{
lean_object* v_declName_654_; 
v_declName_654_ = lean_ctor_get(v_key_638_, 0);
lean_inc(v_declName_654_);
v___y_644_ = v___y_653_;
v___y_645_ = v_declName_654_;
goto v___jp_643_;
}
}
}
case 1:
{
lean_object* v_node_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_669_; 
v_node_657_ = lean_ctor_get(v_v_629_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v_v_629_);
if (v_isSharedCheck_669_ == 0)
{
v___x_659_ = v_v_629_;
v_isShared_660_ = v_isSharedCheck_669_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_node_657_);
lean_dec(v_v_629_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_669_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_661_ = ((size_t)5ULL);
v___x_662_ = lean_usize_shift_right(v_x_616_, v___x_661_);
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_add(v_x_617_, v___x_663_);
v___x_665_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_node_657_, v___x_662_, v___x_664_, v_x_618_, v_x_619_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_665_);
v___x_667_ = v___x_659_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
v___y_633_ = v___x_667_;
goto v___jp_632_;
}
}
}
default: 
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_x_618_);
lean_ctor_set(v___x_670_, 1, v_x_619_);
v___y_633_ = v___x_670_;
goto v___jp_632_;
}
}
v___jp_632_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = lean_array_fset(v_xs_x27_631_, v_j_623_, v___y_633_);
lean_dec(v_j_623_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_634_);
v___x_636_ = v___x_627_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
else
{
lean_object* v_ks_673_; lean_object* v_vs_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_694_; 
v_ks_673_ = lean_ctor_get(v_x_615_, 0);
v_vs_674_ = lean_ctor_get(v_x_615_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_694_ == 0)
{
v___x_676_ = v_x_615_;
v_isShared_677_ = v_isSharedCheck_694_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_vs_674_);
lean_inc(v_ks_673_);
lean_dec(v_x_615_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_694_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_ks_673_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_vs_674_);
v___x_679_ = v_reuseFailAlloc_693_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v_newNode_680_; uint8_t v___y_682_; size_t v___x_688_; uint8_t v___x_689_; 
v_newNode_680_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(v___x_679_, v_x_618_, v_x_619_);
v___x_688_ = ((size_t)7ULL);
v___x_689_ = lean_usize_dec_le(v___x_688_, v_x_617_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_680_);
v___x_691_ = lean_unsigned_to_nat(4u);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
lean_dec(v___x_690_);
v___y_682_ = v___x_692_;
goto v___jp_681_;
}
else
{
v___y_682_ = v___x_689_;
goto v___jp_681_;
}
v___jp_681_:
{
if (v___y_682_ == 0)
{
lean_object* v_ks_683_; lean_object* v_vs_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_ks_683_ = lean_ctor_get(v_newNode_680_, 0);
lean_inc_ref(v_ks_683_);
v_vs_684_ = lean_ctor_get(v_newNode_680_, 1);
lean_inc_ref(v_vs_684_);
lean_dec_ref(v_newNode_680_);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___closed__0);
v___x_687_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_x_617_, v_ks_683_, v_vs_684_, v___x_685_, v___x_686_);
lean_dec_ref(v_vs_684_);
lean_dec_ref(v_ks_683_);
return v___x_687_;
}
else
{
return v_newNode_680_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(size_t v_depth_695_, lean_object* v_keys_696_, lean_object* v_vals_697_, lean_object* v_i_698_, lean_object* v_entries_699_){
_start:
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_array_get_size(v_keys_696_);
v___x_701_ = lean_nat_dec_lt(v_i_698_, v___x_700_);
if (v___x_701_ == 0)
{
lean_dec(v_i_698_);
return v_entries_699_;
}
else
{
lean_object* v_k_702_; lean_object* v_v_703_; uint64_t v___y_705_; lean_object* v___y_717_; lean_object* v_declName_720_; 
v_k_702_ = lean_array_fget_borrowed(v_keys_696_, v_i_698_);
v_v_703_ = lean_array_fget_borrowed(v_vals_697_, v_i_698_);
v_declName_720_ = lean_ctor_get(v_k_702_, 0);
lean_inc(v_declName_720_);
v___y_717_ = v_declName_720_;
goto v___jp_716_;
v___jp_704_:
{
size_t v_h_706_; size_t v___x_707_; lean_object* v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v_h_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_h_706_ = lean_uint64_to_usize(v___y_705_);
v___x_707_ = ((size_t)5ULL);
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = ((size_t)1ULL);
v___x_710_ = lean_usize_sub(v_depth_695_, v___x_709_);
v___x_711_ = lean_usize_mul(v___x_707_, v___x_710_);
v_h_712_ = lean_usize_shift_right(v_h_706_, v___x_711_);
v___x_713_ = lean_nat_add(v_i_698_, v___x_708_);
lean_dec(v_i_698_);
lean_inc(v_v_703_);
lean_inc(v_k_702_);
v___x_714_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_entries_699_, v_h_712_, v_depth_695_, v_k_702_, v_v_703_);
v_i_698_ = v___x_713_;
v_entries_699_ = v___x_714_;
goto _start;
}
v___jp_716_:
{
if (lean_obj_tag(v___y_717_) == 0)
{
uint64_t v___x_718_; 
v___x_718_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0, &l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0);
v___y_705_ = v___x_718_;
goto v___jp_704_;
}
else
{
uint64_t v_hash_719_; 
v_hash_719_ = lean_ctor_get_uint64(v___y_717_, sizeof(void*)*2);
lean_dec(v___y_717_);
v___y_705_ = v_hash_719_;
goto v___jp_704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_721_, lean_object* v_keys_722_, lean_object* v_vals_723_, lean_object* v_i_724_, lean_object* v_entries_725_){
_start:
{
size_t v_depth_boxed_726_; lean_object* v_res_727_; 
v_depth_boxed_726_ = lean_unbox_usize(v_depth_721_);
lean_dec(v_depth_721_);
v_res_727_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_depth_boxed_726_, v_keys_722_, v_vals_723_, v_i_724_, v_entries_725_);
lean_dec_ref(v_vals_723_);
lean_dec_ref(v_keys_722_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg___boxed(lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
size_t v_x_885__boxed_733_; size_t v_x_886__boxed_734_; lean_object* v_res_735_; 
v_x_885__boxed_733_ = lean_unbox_usize(v_x_729_);
lean_dec(v_x_729_);
v_x_886__boxed_734_ = lean_unbox_usize(v_x_730_);
lean_dec(v_x_730_);
v_res_735_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_728_, v_x_885__boxed_733_, v_x_886__boxed_734_, v_x_731_, v_x_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
uint64_t v___y_740_; lean_object* v___y_745_; lean_object* v_declName_748_; 
v_declName_748_ = lean_ctor_get(v_x_737_, 0);
lean_inc(v_declName_748_);
v___y_745_ = v_declName_748_;
goto v___jp_744_;
v___jp_739_:
{
size_t v___x_741_; size_t v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_uint64_to_usize(v___y_740_);
v___x_742_ = ((size_t)1ULL);
v___x_743_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_736_, v___x_741_, v___x_742_, v_x_737_, v_x_738_);
return v___x_743_;
}
v___jp_744_:
{
if (lean_obj_tag(v___y_745_) == 0)
{
uint64_t v___x_746_; 
v___x_746_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0, &l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0);
v___y_740_ = v___x_746_;
goto v___jp_739_;
}
else
{
uint64_t v_hash_747_; 
v_hash_747_ = lean_ctor_get_uint64(v___y_745_, sizeof(void*)*2);
lean_dec(v___y_745_);
v___y_740_ = v_hash_747_;
goto v___jp_739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase___redArg(lean_object* v_s_749_, lean_object* v_origin_750_){
_start:
{
lean_object* v_smap_751_; lean_object* v_origins_752_; lean_object* v_erased_753_; lean_object* v_omap_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_764_; 
v_smap_751_ = lean_ctor_get(v_s_749_, 0);
v_origins_752_ = lean_ctor_get(v_s_749_, 1);
v_erased_753_ = lean_ctor_get(v_s_749_, 2);
v_omap_754_ = lean_ctor_get(v_s_749_, 3);
v_isSharedCheck_764_ = !lean_is_exclusive(v_s_749_);
if (v_isSharedCheck_764_ == 0)
{
v___x_756_ = v_s_749_;
v_isShared_757_ = v_isSharedCheck_764_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_omap_754_);
lean_inc(v_erased_753_);
lean_inc(v_origins_752_);
lean_inc(v_smap_751_);
lean_dec(v_s_749_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_764_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_758_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_origins_752_, v_origin_750_);
v___x_759_ = lean_box(0);
v___x_760_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(v_erased_753_, v_origin_750_, v___x_759_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 2, v___x_760_);
lean_ctor_set(v___x_756_, 1, v___x_758_);
v___x_762_ = v___x_756_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_smap_751_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_omap_754_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_erase(lean_object* v_00_u03b1_765_, lean_object* v_s_766_, lean_object* v_origin_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_s_766_, v_origin_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(lean_object* v_00_u03b2_769_, lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___redArg(v_x_770_, v_x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0___boxed(lean_object* v_00_u03b2_773_, lean_object* v_x_774_, lean_object* v_x_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0(v_00_u03b2_773_, v_x_774_, v_x_775_);
lean_dec_ref(v_x_775_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1(lean_object* v_00_u03b2_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1___redArg(v_x_778_, v_x_779_, v_x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(lean_object* v_00_u03b2_782_, lean_object* v_x_783_, size_t v_x_784_, lean_object* v_x_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___redArg(v_x_783_, v_x_784_, v_x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
size_t v_x_1137__boxed_791_; lean_object* v_res_792_; 
v_x_1137__boxed_791_ = lean_unbox_usize(v_x_789_);
lean_dec(v_x_789_);
v_res_792_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_erase_spec__0_spec__0(v_00_u03b2_787_, v_x_788_, v_x_1137__boxed_791_, v_x_790_);
lean_dec_ref(v_x_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(lean_object* v_00_u03b2_793_, lean_object* v_x_794_, size_t v_x_795_, size_t v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___redArg(v_x_794_, v_x_795_, v_x_796_, v_x_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2___boxed(lean_object* v_00_u03b2_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
size_t v_x_1148__boxed_806_; size_t v_x_1149__boxed_807_; lean_object* v_res_808_; 
v_x_1148__boxed_806_ = lean_unbox_usize(v_x_802_);
lean_dec(v_x_802_);
v_x_1149__boxed_807_ = lean_unbox_usize(v_x_803_);
lean_dec(v_x_803_);
v_res_808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2(v_00_u03b2_800_, v_x_801_, v_x_1148__boxed_806_, v_x_1149__boxed_807_, v_x_804_, v_x_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_809_, lean_object* v_n_810_, lean_object* v_k_811_, lean_object* v_v_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4___redArg(v_n_810_, v_k_811_, v_v_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_814_, size_t v_depth_815_, lean_object* v_keys_816_, lean_object* v_vals_817_, lean_object* v_heq_818_, lean_object* v_i_819_, lean_object* v_entries_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___redArg(v_depth_815_, v_keys_816_, v_vals_817_, v_i_819_, v_entries_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_822_, lean_object* v_depth_823_, lean_object* v_keys_824_, lean_object* v_vals_825_, lean_object* v_heq_826_, lean_object* v_i_827_, lean_object* v_entries_828_){
_start:
{
size_t v_depth_boxed_829_; lean_object* v_res_830_; 
v_depth_boxed_829_ = lean_unbox_usize(v_depth_823_);
lean_dec(v_depth_823_);
v_res_830_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__5(v_00_u03b2_822_, v_depth_boxed_829_, v_keys_824_, v_vals_825_, v_heq_826_, v_i_827_, v_entries_828_);
lean_dec_ref(v_vals_825_);
lean_dec_ref(v_keys_824_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_831_, lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_erase_spec__1_spec__2_spec__4_spec__6___redArg(v_x_832_, v_x_833_, v_x_834_, v_x_835_);
return v___x_836_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_isErased___redArg(lean_object* v_s_837_, lean_object* v_origin_838_){
_start:
{
lean_object* v_erased_839_; uint8_t v___x_840_; 
v_erased_839_ = lean_ctor_get(v_s_837_, 2);
v___x_840_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_erased_839_, v_origin_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___redArg___boxed(lean_object* v_s_841_, lean_object* v_origin_842_){
_start:
{
uint8_t v_res_843_; lean_object* v_r_844_; 
v_res_843_ = l_Lean_Meta_Grind_Theorems_isErased___redArg(v_s_841_, v_origin_842_);
lean_dec_ref(v_origin_842_);
lean_dec_ref(v_s_841_);
v_r_844_ = lean_box(v_res_843_);
return v_r_844_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Theorems_isErased(lean_object* v_00_u03b1_845_, lean_object* v_s_846_, lean_object* v_origin_847_){
_start:
{
uint8_t v___x_848_; 
v___x_848_ = l_Lean_Meta_Grind_Theorems_isErased___redArg(v_s_846_, v_origin_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_isErased___boxed(lean_object* v_00_u03b1_849_, lean_object* v_s_850_, lean_object* v_origin_851_){
_start:
{
uint8_t v_res_852_; lean_object* v_r_853_; 
v_res_852_ = l_Lean_Meta_Grind_Theorems_isErased(v_00_u03b1_849_, v_s_850_, v_origin_851_);
lean_dec_ref(v_origin_851_);
lean_dec_ref(v_s_850_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f___redArg(lean_object* v_s_854_, lean_object* v_sym_855_){
_start:
{
lean_object* v_smap_856_; lean_object* v_origins_857_; lean_object* v_erased_858_; lean_object* v_omap_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_880_; 
v_smap_856_ = lean_ctor_get(v_s_854_, 0);
v_origins_857_ = lean_ctor_get(v_s_854_, 1);
v_erased_858_ = lean_ctor_get(v_s_854_, 2);
v_omap_859_ = lean_ctor_get(v_s_854_, 3);
v_isSharedCheck_880_ = !lean_is_exclusive(v_s_854_);
if (v_isSharedCheck_880_ == 0)
{
v___x_861_ = v_s_854_;
v_isShared_862_ = v_isSharedCheck_880_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_omap_859_);
lean_inc(v_erased_858_);
lean_inc(v_origins_857_);
lean_inc(v_smap_856_);
lean_dec(v_s_854_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_880_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_864_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_855_);
v___x_865_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_863_, v___x_864_, v_smap_856_, v_sym_855_);
if (lean_obj_tag(v___x_865_) == 1)
{
lean_object* v_val_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_878_; 
v_val_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_878_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_878_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_val_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_878_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = l_Lean_PersistentHashMap_erase___redArg(v___x_863_, v___x_864_, v_smap_856_, v_sym_855_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_870_);
v___x_872_ = v___x_861_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_origins_857_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_erased_858_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v_omap_859_);
v___x_872_ = v_reuseFailAlloc_877_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_val_866_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_873_);
v___x_875_ = v___x_868_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v___x_879_; 
lean_dec(v___x_865_);
lean_del_object(v___x_861_);
lean_dec_ref(v_omap_859_);
lean_dec_ref(v_erased_858_);
lean_dec_ref(v_origins_857_);
lean_dec_ref(v_smap_856_);
lean_dec(v_sym_855_);
v___x_879_ = lean_box(0);
return v___x_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_retrieve_x3f(lean_object* v_00_u03b1_881_, lean_object* v_s_882_, lean_object* v_sym_883_){
_start:
{
lean_object* v_smap_884_; lean_object* v_origins_885_; lean_object* v_erased_886_; lean_object* v_omap_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_908_; 
v_smap_884_ = lean_ctor_get(v_s_882_, 0);
v_origins_885_ = lean_ctor_get(v_s_882_, 1);
v_erased_886_ = lean_ctor_get(v_s_882_, 2);
v_omap_887_ = lean_ctor_get(v_s_882_, 3);
v_isSharedCheck_908_ = !lean_is_exclusive(v_s_882_);
if (v_isSharedCheck_908_ == 0)
{
v___x_889_ = v_s_882_;
v_isShared_890_ = v_isSharedCheck_908_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_omap_887_);
lean_inc(v_erased_886_);
lean_inc(v_origins_885_);
lean_inc(v_smap_884_);
lean_dec(v_s_882_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_908_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_892_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_883_);
v___x_893_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_891_, v___x_892_, v_smap_884_, v_sym_883_);
if (lean_obj_tag(v___x_893_) == 1)
{
lean_object* v_val_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_906_; 
v_val_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_906_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_906_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_val_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_906_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = l_Lean_PersistentHashMap_erase___redArg(v___x_891_, v___x_892_, v_smap_884_, v_sym_883_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_898_);
v___x_900_ = v___x_889_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_origins_885_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_erased_886_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_omap_887_);
v___x_900_ = v_reuseFailAlloc_905_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v_val_894_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_901_);
v___x_903_ = v___x_896_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
lean_object* v___x_907_; 
lean_dec(v___x_893_);
lean_del_object(v___x_889_);
lean_dec_ref(v_omap_887_);
lean_dec_ref(v_erased_886_);
lean_dec_ref(v_origins_885_);
lean_dec_ref(v_smap_884_);
lean_dec(v_sym_883_);
v___x_907_ = lean_box(0);
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_909_, lean_object* v_vals_910_, lean_object* v_i_911_, lean_object* v_k_912_){
_start:
{
lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_922_ = lean_array_get_size(v_keys_909_);
v___x_923_ = lean_nat_dec_lt(v_i_911_, v___x_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
lean_dec(v_i_911_);
v___x_924_ = lean_box(0);
return v___x_924_;
}
else
{
lean_object* v_k_x27_925_; lean_object* v___y_927_; lean_object* v_declName_929_; 
v_k_x27_925_ = lean_array_fget_borrowed(v_keys_909_, v_i_911_);
v_declName_929_ = lean_ctor_get(v_k_912_, 0);
v___y_927_ = v_declName_929_;
goto v___jp_926_;
v___jp_926_:
{
lean_object* v_declName_928_; 
v_declName_928_ = lean_ctor_get(v_k_x27_925_, 0);
v___y_914_ = v___y_927_;
v___y_915_ = v_declName_928_;
goto v___jp_913_;
}
}
v___jp_913_:
{
uint8_t v___x_916_; 
v___x_916_ = lean_name_eq(v___y_914_, v___y_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_unsigned_to_nat(1u);
v___x_918_ = lean_nat_add(v_i_911_, v___x_917_);
lean_dec(v_i_911_);
v_i_911_ = v___x_918_;
goto _start;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_array_fget_borrowed(v_vals_910_, v_i_911_);
lean_dec(v_i_911_);
lean_inc(v___x_920_);
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_930_, lean_object* v_vals_931_, lean_object* v_i_932_, lean_object* v_k_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_keys_930_, v_vals_931_, v_i_932_, v_k_933_);
lean_dec_ref(v_k_933_);
lean_dec_ref(v_vals_931_);
lean_dec_ref(v_keys_930_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(lean_object* v_x_935_, size_t v_x_936_, lean_object* v_x_937_){
_start:
{
if (lean_obj_tag(v_x_935_) == 0)
{
lean_object* v_es_938_; lean_object* v___x_939_; size_t v___x_940_; size_t v___x_941_; lean_object* v_j_942_; lean_object* v___x_943_; 
v_es_938_ = lean_ctor_get(v_x_935_, 0);
v___x_939_ = lean_box(2);
v___x_940_ = ((size_t)31ULL);
v___x_941_ = lean_usize_land(v_x_936_, v___x_940_);
v_j_942_ = lean_usize_to_nat(v___x_941_);
v___x_943_ = lean_array_get_borrowed(v___x_939_, v_es_938_, v_j_942_);
lean_dec(v_j_942_);
switch(lean_obj_tag(v___x_943_))
{
case 0:
{
lean_object* v_key_944_; lean_object* v_val_945_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_953_; lean_object* v_declName_955_; 
v_key_944_ = lean_ctor_get(v___x_943_, 0);
v_val_945_ = lean_ctor_get(v___x_943_, 1);
v_declName_955_ = lean_ctor_get(v_x_937_, 0);
v___y_953_ = v_declName_955_;
goto v___jp_952_;
v___jp_946_:
{
uint8_t v___x_949_; 
v___x_949_ = lean_name_eq(v___y_947_, v___y_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
v___x_950_ = lean_box(0);
return v___x_950_;
}
else
{
lean_object* v___x_951_; 
lean_inc(v_val_945_);
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v_val_945_);
return v___x_951_;
}
}
v___jp_952_:
{
lean_object* v_declName_954_; 
v_declName_954_ = lean_ctor_get(v_key_944_, 0);
v___y_947_ = v___y_953_;
v___y_948_ = v_declName_954_;
goto v___jp_946_;
}
}
case 1:
{
lean_object* v_node_956_; size_t v___x_957_; size_t v___x_958_; 
v_node_956_ = lean_ctor_get(v___x_943_, 0);
v___x_957_ = ((size_t)5ULL);
v___x_958_ = lean_usize_shift_right(v_x_936_, v___x_957_);
v_x_935_ = v_node_956_;
v_x_936_ = v___x_958_;
goto _start;
}
default: 
{
lean_object* v___x_960_; 
v___x_960_ = lean_box(0);
return v___x_960_;
}
}
}
else
{
lean_object* v_ks_961_; lean_object* v_vs_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_ks_961_ = lean_ctor_get(v_x_935_, 0);
v_vs_962_ = lean_ctor_get(v_x_935_, 1);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_ks_961_, v_vs_962_, v___x_963_, v_x_937_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg___boxed(lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
size_t v_x_228__boxed_968_; lean_object* v_res_969_; 
v_x_228__boxed_968_ = lean_unbox_usize(v_x_966_);
lean_dec(v_x_966_);
v_res_969_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_965_, v_x_228__boxed_968_, v_x_967_);
lean_dec_ref(v_x_967_);
lean_dec_ref(v_x_965_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(lean_object* v_x_970_, lean_object* v_x_971_){
_start:
{
uint64_t v___y_973_; lean_object* v___y_977_; lean_object* v_declName_980_; 
v_declName_980_ = lean_ctor_get(v_x_971_, 0);
v___y_977_ = v_declName_980_;
goto v___jp_976_;
v___jp_972_:
{
size_t v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_uint64_to_usize(v___y_973_);
v___x_975_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_970_, v___x_974_, v_x_971_);
return v___x_975_;
}
v___jp_976_:
{
if (lean_obj_tag(v___y_977_) == 0)
{
uint64_t v___x_978_; 
v___x_978_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0, &l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instHashableOrigin___lam__0___closed__0);
v___y_973_ = v___x_978_;
goto v___jp_972_;
}
else
{
uint64_t v_hash_979_; 
v_hash_979_ = lean_ctor_get_uint64(v___y_977_, sizeof(void*)*2);
v___y_973_ = v_hash_979_;
goto v___jp_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg___boxed(lean_object* v_x_981_, lean_object* v_x_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_x_981_, v_x_982_);
lean_dec_ref(v_x_982_);
lean_dec_ref(v_x_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg(lean_object* v_s_984_, lean_object* v_origin_985_){
_start:
{
lean_object* v_omap_986_; lean_object* v___x_987_; 
v_omap_986_ = lean_ctor_get(v_s_984_, 3);
v___x_987_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_omap_986_, v_origin_985_);
if (lean_obj_tag(v___x_987_) == 1)
{
lean_object* v_val_988_; 
v_val_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_val_988_);
lean_dec_ref_known(v___x_987_, 1);
return v_val_988_;
}
else
{
lean_object* v___x_989_; 
lean_dec(v___x_987_);
v___x_989_ = lean_box(0);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___redArg___boxed(lean_object* v_s_990_, lean_object* v_origin_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_s_990_, v_origin_991_);
lean_dec_ref(v_origin_991_);
lean_dec_ref(v_s_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find(lean_object* v_00_u03b1_993_, lean_object* v_s_994_, lean_object* v_origin_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_s_994_, v_origin_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_find___boxed(lean_object* v_00_u03b1_997_, lean_object* v_s_998_, lean_object* v_origin_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Meta_Grind_Theorems_find(v_00_u03b1_997_, v_s_998_, v_origin_999_);
lean_dec_ref(v_origin_999_);
lean_dec_ref(v_s_998_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(lean_object* v_00_u03b2_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___redArg(v_x_1002_, v_x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0___boxed(lean_object* v_00_u03b2_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0(v_00_u03b2_1005_, v_x_1006_, v_x_1007_);
lean_dec_ref(v_x_1007_);
lean_dec_ref(v_x_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(lean_object* v_00_u03b2_1009_, lean_object* v_x_1010_, size_t v_x_1011_, lean_object* v_x_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___redArg(v_x_1010_, v_x_1011_, v_x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
size_t v_x_342__boxed_1018_; lean_object* v_res_1019_; 
v_x_342__boxed_1018_ = lean_unbox_usize(v_x_1016_);
lean_dec(v_x_1016_);
v_res_1019_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0(v_00_u03b2_1014_, v_x_1015_, v_x_342__boxed_1018_, v_x_1017_);
lean_dec_ref(v_x_1017_);
lean_dec_ref(v_x_1015_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1020_, lean_object* v_keys_1021_, lean_object* v_vals_1022_, lean_object* v_heq_1023_, lean_object* v_i_1024_, lean_object* v_k_1025_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___redArg(v_keys_1021_, v_vals_1022_, v_i_1024_, v_k_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1027_, lean_object* v_keys_1028_, lean_object* v_vals_1029_, lean_object* v_heq_1030_, lean_object* v_i_1031_, lean_object* v_k_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_find_spec__0_spec__0_spec__1(v_00_u03b2_1027_, v_keys_1028_, v_vals_1029_, v_heq_1030_, v_i_1031_, v_k_1032_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_vals_1029_);
lean_dec_ref(v_keys_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(lean_object* v_x_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0___boxed(lean_object* v_x_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___lam__0(v_x_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v_x_1041_);
return v_res_1047_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1(void){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_instMonadEIO(lean_box(0));
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__1);
v___x_1051_ = l_StateRefT_x27_instMonad___redArg(v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___f_1057_; 
v___x_1056_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1057_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1057_, 0, v___x_1056_);
return v___f_1057_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___f_1059_; 
v___x_1058_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___f_1059_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1059_, 0, v___x_1058_);
return v___f_1059_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9(void){
_start:
{
lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; 
v___f_1060_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__8);
v___f_1061_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__7);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___f_1061_);
lean_ctor_set(v___x_1062_, 1, v___f_1060_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___f_1064_; 
v___x_1063_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9);
v___f_1064_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1064_, 0, v___x_1063_);
return v___f_1064_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___f_1066_; 
v___x_1065_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__9);
v___f_1066_ = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1066_, 0, v___x_1065_);
return v___f_1066_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12(void){
_start:
{
lean_object* v___f_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; 
v___f_1067_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__11);
v___f_1068_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__10);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___f_1068_);
lean_ctor_set(v___x_1069_, 1, v___f_1067_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1074_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1075_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__16));
v___x_1076_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__15));
v___x_1077_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1076_, v___x_1075_, v___x_1074_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___f_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; 
v___x_1078_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__17);
v___f_1079_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__14));
v___f_1080_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__13));
v___x_1081_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1080_, v___f_1079_, v___x_1078_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(lean_object* v_inst_1082_, lean_object* v_thm_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_getProof_1089_; lean_object* v_getLevelParams_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1253_; 
v_getProof_1089_ = lean_ctor_get(v_inst_1082_, 3);
v_getLevelParams_1090_ = lean_ctor_get(v_inst_1082_, 4);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_inst_1082_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; lean_object* v_unused_1255_; lean_object* v_unused_1256_; 
v_unused_1254_ = lean_ctor_get(v_inst_1082_, 2);
lean_dec(v_unused_1254_);
v_unused_1255_ = lean_ctor_get(v_inst_1082_, 1);
lean_dec(v_unused_1255_);
v_unused_1256_ = lean_ctor_get(v_inst_1082_, 0);
lean_dec(v_unused_1256_);
v___x_1092_ = v_inst_1082_;
v_isShared_1093_ = v_isSharedCheck_1253_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_getLevelParams_1090_);
lean_inc(v_getProof_1089_);
lean_dec(v_inst_1082_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1253_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___f_1094_; lean_object* v_proof_1095_; lean_object* v_us_1096_; uint8_t v___y_1098_; uint8_t v___x_1249_; 
v___f_1094_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__0));
lean_inc(v_thm_1083_);
v_proof_1095_ = lean_apply_1(v_getProof_1089_, v_thm_1083_);
v_us_1096_ = lean_apply_1(v_getLevelParams_1090_, v_thm_1083_);
v___x_1249_ = l_Lean_Expr_isConst(v_proof_1095_);
if (v___x_1249_ == 0)
{
v___y_1098_ = v___x_1249_;
goto v___jp_1097_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = lean_array_get_size(v_us_1096_);
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = lean_nat_dec_eq(v___x_1250_, v___x_1251_);
v___y_1098_ = v___x_1252_;
goto v___jp_1097_;
}
v___jp_1097_:
{
if (v___y_1098_ == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = lean_array_get_size(v_us_1096_);
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_nat_dec_eq(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v_toApplicative_1103_; lean_object* v_toFunctor_1104_; lean_object* v_toSeq_1105_; lean_object* v_toSeqLeft_1106_; lean_object* v_toSeqRight_1107_; lean_object* v___f_1108_; lean_object* v___f_1109_; lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___f_1115_; lean_object* v___x_1117_; 
v___x_1102_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2);
v_toApplicative_1103_ = lean_ctor_get(v___x_1102_, 0);
v_toFunctor_1104_ = lean_ctor_get(v_toApplicative_1103_, 0);
v_toSeq_1105_ = lean_ctor_get(v_toApplicative_1103_, 2);
v_toSeqLeft_1106_ = lean_ctor_get(v_toApplicative_1103_, 3);
v_toSeqRight_1107_ = lean_ctor_get(v_toApplicative_1103_, 4);
v___f_1108_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3));
v___f_1109_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4));
lean_inc_ref_n(v_toFunctor_1104_, 2);
v___f_1110_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1110_, 0, v_toFunctor_1104_);
v___f_1111_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1111_, 0, v_toFunctor_1104_);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___f_1110_);
lean_ctor_set(v___x_1112_, 1, v___f_1111_);
lean_inc(v_toSeqRight_1107_);
v___f_1113_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1113_, 0, v_toSeqRight_1107_);
lean_inc(v_toSeqLeft_1106_);
v___f_1114_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1114_, 0, v_toSeqLeft_1106_);
lean_inc(v_toSeq_1105_);
v___f_1115_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1115_, 0, v_toSeq_1105_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v___f_1113_);
lean_ctor_set(v___x_1092_, 3, v___f_1114_);
lean_ctor_set(v___x_1092_, 2, v___f_1115_);
lean_ctor_set(v___x_1092_, 1, v___f_1108_);
lean_ctor_set(v___x_1092_, 0, v___x_1112_);
v___x_1117_ = v___x_1092_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___f_1108_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v___f_1115_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v___f_1114_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v___f_1113_);
v___x_1117_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_toApplicative_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1168_; 
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v___f_1109_);
v___x_1119_ = l_StateRefT_x27_instMonad___redArg(v___x_1118_);
v_toApplicative_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; 
v_unused_1169_ = lean_ctor_get(v___x_1119_, 1);
lean_dec(v_unused_1169_);
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1168_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_toApplicative_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1168_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_toFunctor_1124_; lean_object* v_toSeq_1125_; lean_object* v_toSeqLeft_1126_; lean_object* v_toSeqRight_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1166_; 
v_toFunctor_1124_ = lean_ctor_get(v_toApplicative_1120_, 0);
v_toSeq_1125_ = lean_ctor_get(v_toApplicative_1120_, 2);
v_toSeqLeft_1126_ = lean_ctor_get(v_toApplicative_1120_, 3);
v_toSeqRight_1127_ = lean_ctor_get(v_toApplicative_1120_, 4);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_toApplicative_1120_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v_toApplicative_1120_, 1);
lean_dec(v_unused_1167_);
v___x_1129_ = v_toApplicative_1120_;
v_isShared_1130_ = v_isSharedCheck_1166_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_toSeqRight_1127_);
lean_inc(v_toSeqLeft_1126_);
lean_inc(v_toSeq_1125_);
lean_inc(v_toFunctor_1124_);
lean_dec(v_toApplicative_1120_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1166_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___f_1133_; lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___x_1140_; 
v___f_1131_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5));
v___f_1132_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6));
lean_inc_ref(v_toFunctor_1124_);
v___f_1133_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1133_, 0, v_toFunctor_1124_);
v___f_1134_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1134_, 0, v_toFunctor_1124_);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___f_1133_);
lean_ctor_set(v___x_1135_, 1, v___f_1134_);
v___f_1136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1136_, 0, v_toSeqRight_1127_);
v___f_1137_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1137_, 0, v_toSeqLeft_1126_);
v___f_1138_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1138_, 0, v_toSeq_1125_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 4, v___f_1136_);
lean_ctor_set(v___x_1129_, 3, v___f_1137_);
lean_ctor_set(v___x_1129_, 2, v___f_1138_);
lean_ctor_set(v___x_1129_, 1, v___f_1131_);
lean_ctor_set(v___x_1129_, 0, v___x_1135_);
v___x_1140_ = v___x_1129_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v___f_1131_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v___f_1138_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v___f_1137_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v___f_1136_);
v___x_1140_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v___f_1132_);
lean_ctor_set(v___x_1122_, 0, v___x_1140_);
v___x_1142_ = v___x_1122_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___f_1132_);
v___x_1142_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
size_t v_sz_1143_; size_t v___x_1144_; lean_object* v___x_898__overap_1145_; lean_object* v___x_1146_; 
v_sz_1143_ = lean_array_size(v_us_1096_);
v___x_1144_ = ((size_t)0ULL);
lean_inc_ref(v_us_1096_);
v___x_898__overap_1145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1142_, v___f_1094_, v_sz_1143_, v___x_1144_, v_us_1096_);
lean_inc(v_a_1087_);
lean_inc_ref(v_a_1086_);
lean_inc(v_a_1085_);
lean_inc_ref(v_a_1084_);
v___x_1146_ = lean_apply_5(v___x_898__overap_1145_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, lean_box(0));
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1155_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = l_Lean_Expr_instantiateLevelParamsArray(v_proof_1095_, v_us_1096_, v_a_1147_);
lean_dec_ref(v_proof_1095_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec_ref(v_us_1096_);
lean_dec_ref(v_proof_1095_);
v_a_1156_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1146_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1146_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
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
lean_object* v___x_1171_; 
lean_dec_ref(v_us_1096_);
lean_del_object(v___x_1092_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_proof_1095_);
return v___x_1171_;
}
}
else
{
lean_object* v___x_1172_; lean_object* v_toApplicative_1173_; lean_object* v_toFunctor_1174_; lean_object* v_toSeq_1175_; lean_object* v_toSeqLeft_1176_; lean_object* v_toSeqRight_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; lean_object* v___f_1183_; lean_object* v___f_1184_; lean_object* v___f_1185_; lean_object* v___x_1187_; 
lean_dec_ref(v_us_1096_);
v___x_1172_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__2);
v_toApplicative_1173_ = lean_ctor_get(v___x_1172_, 0);
v_toFunctor_1174_ = lean_ctor_get(v_toApplicative_1173_, 0);
v_toSeq_1175_ = lean_ctor_get(v_toApplicative_1173_, 2);
v_toSeqLeft_1176_ = lean_ctor_get(v_toApplicative_1173_, 3);
v_toSeqRight_1177_ = lean_ctor_get(v_toApplicative_1173_, 4);
v___f_1178_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__3));
v___f_1179_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__4));
lean_inc_ref_n(v_toFunctor_1174_, 2);
v___f_1180_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1180_, 0, v_toFunctor_1174_);
v___f_1181_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1181_, 0, v_toFunctor_1174_);
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___f_1180_);
lean_ctor_set(v___x_1182_, 1, v___f_1181_);
lean_inc(v_toSeqRight_1177_);
v___f_1183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1183_, 0, v_toSeqRight_1177_);
lean_inc(v_toSeqLeft_1176_);
v___f_1184_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1184_, 0, v_toSeqLeft_1176_);
lean_inc(v_toSeq_1175_);
v___f_1185_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1185_, 0, v_toSeq_1175_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 4, v___f_1183_);
lean_ctor_set(v___x_1092_, 3, v___f_1184_);
lean_ctor_set(v___x_1092_, 2, v___f_1185_);
lean_ctor_set(v___x_1092_, 1, v___f_1178_);
lean_ctor_set(v___x_1092_, 0, v___x_1182_);
v___x_1187_ = v___x_1092_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___f_1178_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v___f_1185_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v___f_1184_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v___f_1183_);
v___x_1187_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_toApplicative_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1246_; 
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v___f_1179_);
v___x_1189_ = l_StateRefT_x27_instMonad___redArg(v___x_1188_);
v_toApplicative_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1189_, 1);
lean_dec(v_unused_1247_);
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1246_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_toApplicative_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1246_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_toFunctor_1194_; lean_object* v_toSeq_1195_; lean_object* v_toSeqLeft_1196_; lean_object* v_toSeqRight_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1244_; 
v_toFunctor_1194_ = lean_ctor_get(v_toApplicative_1190_, 0);
v_toSeq_1195_ = lean_ctor_get(v_toApplicative_1190_, 2);
v_toSeqLeft_1196_ = lean_ctor_get(v_toApplicative_1190_, 3);
v_toSeqRight_1197_ = lean_ctor_get(v_toApplicative_1190_, 4);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_toApplicative_1190_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v_toApplicative_1190_, 1);
lean_dec(v_unused_1245_);
v___x_1199_ = v_toApplicative_1190_;
v_isShared_1200_ = v_isSharedCheck_1244_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_toSeqRight_1197_);
lean_inc(v_toSeqLeft_1196_);
lean_inc(v_toSeq_1195_);
lean_inc(v_toFunctor_1194_);
lean_dec(v_toApplicative_1190_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1244_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1210_; 
v___f_1201_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__5));
v___f_1202_ = ((lean_object*)(l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__6));
lean_inc_ref(v_toFunctor_1194_);
v___f_1203_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1203_, 0, v_toFunctor_1194_);
v___f_1204_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1204_, 0, v_toFunctor_1194_);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___f_1203_);
lean_ctor_set(v___x_1205_, 1, v___f_1204_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toSeqRight_1197_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toSeqLeft_1196_);
v___f_1208_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1208_, 0, v_toSeq_1195_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 4, v___f_1206_);
lean_ctor_set(v___x_1199_, 3, v___f_1207_);
lean_ctor_set(v___x_1199_, 2, v___f_1208_);
lean_ctor_set(v___x_1199_, 1, v___f_1201_);
lean_ctor_set(v___x_1199_, 0, v___x_1205_);
v___x_1210_ = v___x_1199_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___f_1201_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v___f_1208_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v___f_1207_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v___f_1206_);
v___x_1210_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1212_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___f_1202_);
lean_ctor_set(v___x_1192_, 0, v___x_1210_);
v___x_1212_ = v___x_1192_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___f_1202_);
v___x_1212_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_toMonadRef_1216_; lean_object* v_declName_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_886__overap_1221_; lean_object* v___x_1222_; 
v___x_1213_ = l_Lean_Meta_instMonadEnvMetaM;
v___x_1214_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__12);
v___x_1215_ = lean_obj_once(&l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18, &l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18_once, _init_l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___closed__18);
v_toMonadRef_1216_ = lean_ctor_get(v___x_1215_, 0);
v_declName_1217_ = l_Lean_Expr_constName_x21(v_proof_1095_);
v___x_1218_ = l_Lean_Meta_instAddMessageContextMetaM;
lean_inc_ref(v___x_1212_);
v___x_1219_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_1218_, v___x_1212_);
lean_inc_ref(v_toMonadRef_1216_);
v___x_1220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1214_);
lean_ctor_set(v___x_1220_, 1, v_toMonadRef_1216_);
lean_ctor_set(v___x_1220_, 2, v___x_1219_);
lean_inc(v_declName_1217_);
v___x_886__overap_1221_ = l_Lean_getConstVal___redArg(v___x_1212_, v___x_1213_, v___x_1220_, v_declName_1217_);
lean_inc(v_a_1087_);
lean_inc_ref(v_a_1086_);
lean_inc(v_a_1085_);
lean_inc_ref(v_a_1084_);
v___x_1222_ = lean_apply_5(v___x_886__overap_1221_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, lean_box(0));
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1233_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1233_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1233_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_levelParams_1227_; uint8_t v___x_1228_; 
v_levelParams_1227_ = lean_ctor_get(v_a_1223_, 1);
lean_inc(v_levelParams_1227_);
lean_dec(v_a_1223_);
v___x_1228_ = l_List_isEmpty___redArg(v_levelParams_1227_);
lean_dec(v_levelParams_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; 
lean_del_object(v___x_1225_);
lean_dec_ref(v_proof_1095_);
v___x_1229_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_1217_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1229_;
}
else
{
lean_object* v___x_1231_; 
lean_dec(v_declName_1217_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v_proof_1095_);
v___x_1231_ = v___x_1225_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_proof_1095_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_declName_1217_);
lean_dec_ref(v_proof_1095_);
v_a_1234_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1222_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1222_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg___boxed(lean_object* v_inst_1257_, lean_object* v_thm_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(v_inst_1257_, v_thm_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels(lean_object* v_00_u03b1_1265_, lean_object* v_inst_1266_, lean_object* v_thm_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels___redArg(v_inst_1266_, v_thm_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofWithFreshMVarLevels___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_inst_1275_, lean_object* v_thm_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_Meta_Grind_getProofWithFreshMVarLevels(v_00_u03b1_1274_, v_inst_1275_, v_thm_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(lean_object* v_msgData_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; lean_object* v_env_1290_; lean_object* v___x_1291_; lean_object* v_mctx_1292_; lean_object* v_lctx_1293_; lean_object* v_options_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1289_ = lean_st_ref_get(v___y_1287_);
v_env_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc_ref(v_env_1290_);
lean_dec(v___x_1289_);
v___x_1291_ = lean_st_ref_get(v___y_1285_);
v_mctx_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc_ref(v_mctx_1292_);
lean_dec(v___x_1291_);
v_lctx_1293_ = lean_ctor_get(v___y_1284_, 2);
v_options_1294_ = lean_ctor_get(v___y_1286_, 2);
lean_inc_ref(v_options_1294_);
lean_inc_ref(v_lctx_1293_);
v___x_1295_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1295_, 0, v_env_1290_);
lean_ctor_set(v___x_1295_, 1, v_mctx_1292_);
lean_ctor_set(v___x_1295_, 2, v_lctx_1293_);
lean_ctor_set(v___x_1295_, 3, v_options_1294_);
v___x_1296_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v_msgData_1283_);
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0___boxed(lean_object* v_msgData_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(v_msgData_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(lean_object* v_msg_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_ref_1311_; lean_object* v___x_1312_; lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1321_; 
v_ref_1311_ = lean_ctor_get(v___y_1308_, 5);
v___x_1312_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0_spec__0(v_msg_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_inc(v_ref_1311_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v_ref_1311_);
lean_ctor_set(v___x_1317_, 1, v_a_1313_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set_tag(v___x_1315_, 1);
lean_ctor_set(v___x_1315_, 0, v___x_1317_);
v___x_1319_ = v___x_1315_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg___boxed(lean_object* v_msg_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
return v_res_1328_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__0));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__2));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(lean_object* v_declName_1335_, lean_object* v_00_u03b1_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1342_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1);
v___x_1343_ = 0;
v___x_1344_ = l_Lean_MessageData_ofConstName(v_declName_1335_, v___x_1343_);
v___x_1345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1342_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__3);
v___x_1347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v___x_1347_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___boxed(lean_object* v_declName_1349_, lean_object* v_00_u03b1_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1349_, v_00_u03b1_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v_res_1356_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(lean_object* v_s_1357_, lean_object* v_as_1358_, size_t v_i_1359_, size_t v_stop_1360_){
_start:
{
uint8_t v___x_1361_; 
v___x_1361_ = lean_usize_dec_eq(v_i_1359_, v_stop_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; uint8_t v___x_1365_; 
v___x_1362_ = lean_array_uget_borrowed(v_as_1358_, v_i_1359_);
lean_inc(v___x_1362_);
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
v___x_1364_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_1357_, v___x_1363_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1365_ = lean_bool_not(v___x_1364_);
if (v___x_1365_ == 0)
{
size_t v___x_1366_; size_t v___x_1367_; 
v___x_1366_ = ((size_t)1ULL);
v___x_1367_ = lean_usize_add(v_i_1359_, v___x_1366_);
v_i_1359_ = v___x_1367_;
goto _start;
}
else
{
return v___x_1365_;
}
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = 0;
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg___boxed(lean_object* v_s_1370_, lean_object* v_as_1371_, lean_object* v_i_1372_, lean_object* v_stop_1373_){
_start:
{
size_t v_i_boxed_1374_; size_t v_stop_boxed_1375_; uint8_t v_res_1376_; lean_object* v_r_1377_; 
v_i_boxed_1374_ = lean_unbox_usize(v_i_1372_);
lean_dec(v_i_1372_);
v_stop_boxed_1375_ = lean_unbox_usize(v_stop_1373_);
lean_dec(v_stop_1373_);
v_res_1376_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1370_, v_as_1371_, v_i_boxed_1374_, v_stop_boxed_1375_);
lean_dec_ref(v_as_1371_);
lean_dec_ref(v_s_1370_);
v_r_1377_ = lean_box(v_res_1376_);
return v_r_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(lean_object* v_as_1378_, size_t v_i_1379_, size_t v_stop_1380_, lean_object* v_b_1381_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_usize_dec_eq(v_i_1379_, v_stop_1380_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; 
v___x_1383_ = lean_array_uget_borrowed(v_as_1378_, v_i_1379_);
lean_inc(v___x_1383_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
v___x_1385_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_b_1381_, v___x_1384_);
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_add(v_i_1379_, v___x_1386_);
v_i_1379_ = v___x_1387_;
v_b_1381_ = v___x_1385_;
goto _start;
}
else
{
return v_b_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg___boxed(lean_object* v_as_1389_, lean_object* v_i_1390_, lean_object* v_stop_1391_, lean_object* v_b_1392_){
_start:
{
size_t v_i_boxed_1393_; size_t v_stop_boxed_1394_; lean_object* v_res_1395_; 
v_i_boxed_1393_ = lean_unbox_usize(v_i_1390_);
lean_dec(v_i_1390_);
v_stop_boxed_1394_ = lean_unbox_usize(v_stop_1391_);
lean_dec(v_stop_1391_);
v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_as_1389_, v_i_boxed_1393_, v_stop_boxed_1394_, v_b_1392_);
lean_dec_ref(v_as_1389_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object* v_s_1396_, lean_object* v_declName_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1407_; lean_object* v_env_1408_; uint8_t v___x_1409_; uint8_t v___x_1410_; 
v___x_1407_ = lean_st_ref_get(v_a_1401_);
v_env_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc_ref(v_env_1408_);
lean_dec(v___x_1407_);
lean_inc(v_declName_1397_);
v___x_1409_ = l_Lean_wasOriginallyTheorem(v_env_1408_, v_declName_1397_);
v___x_1410_ = lean_bool_not(v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; uint8_t v___x_1412_; 
lean_inc(v_declName_1397_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_declName_1397_);
v___x_1412_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_s_1396_, v___x_1411_);
lean_dec_ref_known(v___x_1411_, 1);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v_s_1396_);
v___x_1413_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1397_, lean_box(0), v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
else
{
goto v___jp_1403_;
}
}
else
{
lean_object* v___x_1422_; 
lean_inc(v_declName_1397_);
v___x_1422_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1472_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1472_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1472_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
if (lean_obj_tag(v_a_1423_) == 1)
{
lean_object* v_val_1427_; uint8_t v___y_1452_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_val_1427_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_val_1427_);
lean_dec_ref_known(v_a_1423_, 1);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_array_get_size(v_val_1427_);
v___x_1464_ = lean_nat_dec_lt(v___x_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
uint8_t v___x_1465_; 
v___x_1465_ = lean_bool_not(v___x_1464_);
v___y_1452_ = v___x_1465_;
goto v___jp_1451_;
}
else
{
if (v___x_1464_ == 0)
{
uint8_t v___x_1466_; 
v___x_1466_ = lean_bool_not(v___x_1464_);
v___y_1452_ = v___x_1466_;
goto v___jp_1451_;
}
else
{
size_t v___x_1467_; size_t v___x_1468_; uint8_t v___x_1469_; uint8_t v___x_1470_; 
v___x_1467_ = ((size_t)0ULL);
v___x_1468_ = lean_usize_of_nat(v___x_1463_);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1396_, v_val_1427_, v___x_1467_, v___x_1468_);
v___x_1470_ = lean_bool_not(v___x_1469_);
v___y_1452_ = v___x_1470_;
goto v___jp_1451_;
}
}
v___jp_1428_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_array_get_size(v_val_1427_);
v___x_1431_ = lean_nat_dec_lt(v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1433_; 
lean_dec(v_val_1427_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v_s_1396_);
v___x_1433_ = v___x_1425_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_s_1396_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
else
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_nat_dec_le(v___x_1430_, v___x_1430_);
if (v___x_1435_ == 0)
{
if (v___x_1431_ == 0)
{
lean_object* v___x_1437_; 
lean_dec(v_val_1427_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v_s_1396_);
v___x_1437_ = v___x_1425_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_s_1396_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
else
{
size_t v___x_1439_; size_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1439_ = ((size_t)0ULL);
v___x_1440_ = lean_usize_of_nat(v___x_1430_);
v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_val_1427_, v___x_1439_, v___x_1440_, v_s_1396_);
lean_dec(v_val_1427_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1441_);
v___x_1443_ = v___x_1425_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
else
{
size_t v___x_1445_; size_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1445_ = ((size_t)0ULL);
v___x_1446_ = lean_usize_of_nat(v___x_1430_);
v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_val_1427_, v___x_1445_, v___x_1446_, v_s_1396_);
lean_dec(v_val_1427_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1447_);
v___x_1449_ = v___x_1425_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
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
v___jp_1451_:
{
if (v___y_1452_ == 0)
{
lean_object* v___x_1453_; lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_val_1427_);
lean_del_object(v___x_1425_);
lean_dec_ref(v_s_1396_);
v___x_1453_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1397_, lean_box(0), v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
else
{
lean_dec(v_declName_1397_);
goto v___jp_1428_;
}
}
}
else
{
lean_object* v___x_1471_; 
lean_del_object(v___x_1425_);
lean_dec(v_a_1423_);
lean_dec_ref(v_s_1396_);
v___x_1471_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0(v_declName_1397_, lean_box(0), v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
return v___x_1471_;
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_declName_1397_);
lean_dec_ref(v_s_1396_);
v_a_1473_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1422_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1422_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
v___jp_1403_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_declName_1397_);
v___x_1405_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_s_1396_, v___x_1404_);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___boxed(lean_object* v_s_1481_, lean_object* v_declName_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_s_1481_, v_declName_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl(lean_object* v_00_u03b1_1489_, lean_object* v_s_1490_, lean_object* v_declName_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_s_1490_, v_declName_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___boxed(lean_object* v_00_u03b1_1498_, lean_object* v_s_1499_, lean_object* v_declName_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Meta_Grind_Theorems_eraseDecl(v_00_u03b1_1498_, v_s_1499_, v_declName_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(lean_object* v_00_u03b1_1507_, lean_object* v_msg_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___boxed(lean_object* v_00_u03b1_1515_, lean_object* v_msg_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0(v_00_u03b1_1515_, v_msg_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(lean_object* v_00_u03b1_1523_, lean_object* v_as_1524_, size_t v_i_1525_, size_t v_stop_1526_, lean_object* v_b_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___redArg(v_as_1524_, v_i_1525_, v_stop_1526_, v_b_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1___boxed(lean_object* v_00_u03b1_1529_, lean_object* v_as_1530_, lean_object* v_i_1531_, lean_object* v_stop_1532_, lean_object* v_b_1533_){
_start:
{
size_t v_i_boxed_1534_; size_t v_stop_boxed_1535_; lean_object* v_res_1536_; 
v_i_boxed_1534_ = lean_unbox_usize(v_i_1531_);
lean_dec(v_i_1531_);
v_stop_boxed_1535_ = lean_unbox_usize(v_stop_1532_);
lean_dec(v_stop_1532_);
v_res_1536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__1(v_00_u03b1_1529_, v_as_1530_, v_i_boxed_1534_, v_stop_boxed_1535_, v_b_1533_);
lean_dec_ref(v_as_1530_);
return v_res_1536_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(lean_object* v_00_u03b1_1537_, lean_object* v_s_1538_, lean_object* v_as_1539_, size_t v_i_1540_, size_t v_stop_1541_){
_start:
{
uint8_t v___x_1542_; 
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___redArg(v_s_1538_, v_as_1539_, v_i_1540_, v_stop_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2___boxed(lean_object* v_00_u03b1_1543_, lean_object* v_s_1544_, lean_object* v_as_1545_, lean_object* v_i_1546_, lean_object* v_stop_1547_){
_start:
{
size_t v_i_boxed_1548_; size_t v_stop_boxed_1549_; uint8_t v_res_1550_; lean_object* v_r_1551_; 
v_i_boxed_1548_ = lean_unbox_usize(v_i_1546_);
lean_dec(v_i_1546_);
v_stop_boxed_1549_ = lean_unbox_usize(v_stop_1547_);
lean_dec(v_stop_1547_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__2(v_00_u03b1_1543_, v_s_1544_, v_as_1545_, v_i_boxed_1548_, v_stop_boxed_1549_);
lean_dec_ref(v_as_1545_);
lean_dec_ref(v_s_1544_);
v_r_1551_ = lean_box(v_res_1550_);
return v_r_1551_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
if (lean_obj_tag(v_a_1552_) == 0)
{
lean_object* v___x_1554_; 
v___x_1554_ = l_List_reverse___redArg(v_a_1553_);
return v___x_1554_;
}
else
{
lean_object* v_head_1555_; lean_object* v_tail_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1565_; 
v_head_1555_ = lean_ctor_get(v_a_1552_, 0);
v_tail_1556_ = lean_ctor_get(v_a_1552_, 1);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_a_1552_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1558_ = v_a_1552_;
v_isShared_1559_ = v_isSharedCheck_1565_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_tail_1556_);
lean_inc(v_head_1555_);
lean_dec(v_a_1552_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1565_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v_fst_1560_; lean_object* v___x_1562_; 
v_fst_1560_ = lean_ctor_get(v_head_1555_, 0);
lean_inc(v_fst_1560_);
lean_dec(v_head_1555_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 1, v_a_1553_);
lean_ctor_set(v___x_1558_, 0, v_fst_1560_);
v___x_1562_ = v___x_1558_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_fst_1560_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_a_1553_);
v___x_1562_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
v_a_1552_ = v_tail_1556_;
v_a_1553_ = v___x_1562_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___lam__0(lean_object* v_ps_1566_, lean_object* v_k_1567_, lean_object* v_v_1568_){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_k_1567_);
lean_ctor_set(v___x_1569_, 1, v_v_1568_);
v___x_1570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
lean_ctor_set(v___x_1570_, 1, v_ps_1566_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1571_, lean_object* v_x1_1572_, lean_object* v_x2_1573_, lean_object* v_x3_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_apply_3(v_f_1571_, v_x1_1572_, v_x2_1573_, v_x3_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_f_1576_, lean_object* v_keys_1577_, lean_object* v_vals_1578_, lean_object* v_i_1579_, lean_object* v_acc_1580_){
_start:
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = lean_array_get_size(v_keys_1577_);
v___x_1582_ = lean_nat_dec_lt(v_i_1579_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_dec(v_i_1579_);
lean_dec(v_f_1576_);
return v_acc_1580_;
}
else
{
lean_object* v_k_1583_; lean_object* v_v_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_k_1583_ = lean_array_fget_borrowed(v_keys_1577_, v_i_1579_);
v_v_1584_ = lean_array_fget_borrowed(v_vals_1578_, v_i_1579_);
lean_inc(v_f_1576_);
lean_inc(v_v_1584_);
lean_inc(v_k_1583_);
v___x_1585_ = lean_apply_3(v_f_1576_, v_acc_1580_, v_k_1583_, v_v_1584_);
v___x_1586_ = lean_unsigned_to_nat(1u);
v___x_1587_ = lean_nat_add(v_i_1579_, v___x_1586_);
lean_dec(v_i_1579_);
v_i_1579_ = v___x_1587_;
v_acc_1580_ = v___x_1585_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_f_1589_, lean_object* v_keys_1590_, lean_object* v_vals_1591_, lean_object* v_i_1592_, lean_object* v_acc_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1589_, v_keys_1590_, v_vals_1591_, v_i_1592_, v_acc_1593_);
lean_dec_ref(v_vals_1591_);
lean_dec_ref(v_keys_1590_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_f_1595_, lean_object* v_x_1596_, lean_object* v_x_1597_){
_start:
{
if (lean_obj_tag(v_x_1596_) == 0)
{
lean_object* v_es_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v_es_1598_ = lean_ctor_get(v_x_1596_, 0);
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = lean_array_get_size(v_es_1598_);
v___x_1601_ = lean_nat_dec_lt(v___x_1599_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_dec(v_f_1595_);
return v_x_1597_;
}
else
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_nat_dec_le(v___x_1600_, v___x_1600_);
if (v___x_1602_ == 0)
{
if (v___x_1601_ == 0)
{
lean_dec(v_f_1595_);
return v_x_1597_;
}
else
{
size_t v___x_1603_; size_t v___x_1604_; lean_object* v___x_1605_; 
v___x_1603_ = ((size_t)0ULL);
v___x_1604_ = lean_usize_of_nat(v___x_1600_);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1595_, v_es_1598_, v___x_1603_, v___x_1604_, v_x_1597_);
return v___x_1605_;
}
}
else
{
size_t v___x_1606_; size_t v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = ((size_t)0ULL);
v___x_1607_ = lean_usize_of_nat(v___x_1600_);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1595_, v_es_1598_, v___x_1606_, v___x_1607_, v_x_1597_);
return v___x_1608_;
}
}
}
else
{
lean_object* v_ks_1609_; lean_object* v_vs_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_ks_1609_ = lean_ctor_get(v_x_1596_, 0);
v_vs_1610_ = lean_ctor_get(v_x_1596_, 1);
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1595_, v_ks_1609_, v_vs_1610_, v___x_1611_, v_x_1597_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_f_1613_, lean_object* v_as_1614_, size_t v_i_1615_, size_t v_stop_1616_, lean_object* v_b_1617_){
_start:
{
lean_object* v___y_1619_; uint8_t v___x_1623_; 
v___x_1623_ = lean_usize_dec_eq(v_i_1615_, v_stop_1616_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_array_uget_borrowed(v_as_1614_, v_i_1615_);
switch(lean_obj_tag(v___x_1624_))
{
case 0:
{
lean_object* v_key_1625_; lean_object* v_val_1626_; lean_object* v___x_1627_; 
v_key_1625_ = lean_ctor_get(v___x_1624_, 0);
v_val_1626_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_f_1613_);
lean_inc(v_val_1626_);
lean_inc(v_key_1625_);
v___x_1627_ = lean_apply_3(v_f_1613_, v_b_1617_, v_key_1625_, v_val_1626_);
v___y_1619_ = v___x_1627_;
goto v___jp_1618_;
}
case 1:
{
lean_object* v_node_1628_; lean_object* v___x_1629_; 
v_node_1628_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_f_1613_);
v___x_1629_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1613_, v_node_1628_, v_b_1617_);
v___y_1619_ = v___x_1629_;
goto v___jp_1618_;
}
default: 
{
v___y_1619_ = v_b_1617_;
goto v___jp_1618_;
}
}
}
else
{
lean_dec(v_f_1613_);
return v_b_1617_;
}
v___jp_1618_:
{
size_t v___x_1620_; size_t v___x_1621_; 
v___x_1620_ = ((size_t)1ULL);
v___x_1621_ = lean_usize_add(v_i_1615_, v___x_1620_);
v_i_1615_ = v___x_1621_;
v_b_1617_ = v___y_1619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_f_1630_, lean_object* v_as_1631_, lean_object* v_i_1632_, lean_object* v_stop_1633_, lean_object* v_b_1634_){
_start:
{
size_t v_i_boxed_1635_; size_t v_stop_boxed_1636_; lean_object* v_res_1637_; 
v_i_boxed_1635_ = lean_unbox_usize(v_i_1632_);
lean_dec(v_i_1632_);
v_stop_boxed_1636_ = lean_unbox_usize(v_stop_1633_);
lean_dec(v_stop_1633_);
v_res_1637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1630_, v_as_1631_, v_i_boxed_1635_, v_stop_boxed_1636_, v_b_1634_);
lean_dec_ref(v_as_1631_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_f_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1638_, v_x_1639_, v_x_1640_);
lean_dec_ref(v_x_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(lean_object* v_map_1642_, lean_object* v_f_1643_, lean_object* v_init_1644_){
_start:
{
lean_object* v___f_1645_; lean_object* v___x_1646_; 
v___f_1645_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1645_, 0, v_f_1643_);
v___x_1646_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v___f_1645_, v_map_1642_, v_init_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_1647_, lean_object* v_f_1648_, lean_object* v_init_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_map_1647_, v_f_1648_, v_init_1649_);
lean_dec_ref(v_map_1647_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(lean_object* v_m_1652_){
_start:
{
lean_object* v___f_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___f_1653_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___closed__0));
v___x_1654_ = lean_box(0);
v___x_1655_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_m_1652_, v___f_1653_, v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg___boxed(lean_object* v_m_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_m_1656_);
lean_dec_ref(v_m_1656_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(lean_object* v_s_1658_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_s_1658_);
v___x_1660_ = lean_box(0);
v___x_1661_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__1(v___x_1659_, v___x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0___boxed(lean_object* v_s_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(v_s_1662_);
lean_dec_ref(v_s_1662_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg(lean_object* v_s_1664_){
_start:
{
lean_object* v_origins_1665_; lean_object* v___x_1666_; 
v_origins_1665_ = lean_ctor_get(v_s_1664_, 1);
v___x_1666_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0(v_origins_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg___boxed(lean_object* v_s_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_s_1667_);
lean_dec_ref(v_s_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins(lean_object* v_00_u03b1_1669_, lean_object* v_s_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_s_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___boxed(lean_object* v_00_u03b1_1672_, lean_object* v_s_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Meta_Grind_Theorems_getOrigins(v_00_u03b1_1672_, v_s_1673_);
lean_dec_ref(v_s_1673_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(lean_object* v_00_u03b2_1675_, lean_object* v_m_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___redArg(v_m_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1678_, lean_object* v_m_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0(v_00_u03b2_1678_, v_m_1679_);
lean_dec_ref(v_m_1679_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1681_, lean_object* v_00_u03b2_1682_, lean_object* v_map_1683_, lean_object* v_f_1684_, lean_object* v_init_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___redArg(v_map_1683_, v_f_1684_, v_init_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1687_, lean_object* v_00_u03b2_1688_, lean_object* v_map_1689_, lean_object* v_f_1690_, lean_object* v_init_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1(v_00_u03c3_1687_, v_00_u03b2_1688_, v_map_1689_, v_f_1690_, v_init_1691_);
lean_dec_ref(v_map_1689_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1693_, lean_object* v_f_1694_, lean_object* v_init_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1694_, v_map_1693_, v_init_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1697_, lean_object* v_f_1698_, lean_object* v_init_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___redArg(v_map_1697_, v_f_1698_, v_init_1699_);
lean_dec_ref(v_map_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1701_, lean_object* v_00_u03b2_1702_, lean_object* v_map_1703_, lean_object* v_f_1704_, lean_object* v_init_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1704_, v_map_1703_, v_init_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1707_, lean_object* v_00_u03b2_1708_, lean_object* v_map_1709_, lean_object* v_f_1710_, lean_object* v_init_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2(v_00_u03c3_1707_, v_00_u03b2_1708_, v_map_1709_, v_f_1710_, v_init_1711_);
lean_dec_ref(v_map_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03c3_1713_, lean_object* v_00_u03b1_1714_, lean_object* v_00_u03b2_1715_, lean_object* v_f_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_f_1716_, v_x_1717_, v_x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03c3_1720_, lean_object* v_00_u03b1_1721_, lean_object* v_00_u03b2_1722_, lean_object* v_f_1723_, lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03c3_1720_, v_00_u03b1_1721_, v_00_u03b2_1722_, v_f_1723_, v_x_1724_, v_x_1725_);
lean_dec_ref(v_x_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b1_1727_, lean_object* v_00_u03b2_1728_, lean_object* v_00_u03c3_1729_, lean_object* v_f_1730_, lean_object* v_as_1731_, size_t v_i_1732_, size_t v_stop_1733_, lean_object* v_b_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___redArg(v_f_1730_, v_as_1731_, v_i_1732_, v_stop_1733_, v_b_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1736_, lean_object* v_00_u03b2_1737_, lean_object* v_00_u03c3_1738_, lean_object* v_f_1739_, lean_object* v_as_1740_, lean_object* v_i_1741_, lean_object* v_stop_1742_, lean_object* v_b_1743_){
_start:
{
size_t v_i_boxed_1744_; size_t v_stop_boxed_1745_; lean_object* v_res_1746_; 
v_i_boxed_1744_ = lean_unbox_usize(v_i_1741_);
lean_dec(v_i_1741_);
v_stop_boxed_1745_ = lean_unbox_usize(v_stop_1742_);
lean_dec(v_stop_1742_);
v_res_1746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__5(v_00_u03b1_1736_, v_00_u03b2_1737_, v_00_u03c3_1738_, v_f_1739_, v_as_1740_, v_i_boxed_1744_, v_stop_boxed_1745_, v_b_1743_);
lean_dec_ref(v_as_1740_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03c3_1747_, lean_object* v_00_u03b1_1748_, lean_object* v_00_u03b2_1749_, lean_object* v_f_1750_, lean_object* v_keys_1751_, lean_object* v_vals_1752_, lean_object* v_heq_1753_, lean_object* v_i_1754_, lean_object* v_acc_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_f_1750_, v_keys_1751_, v_vals_1752_, v_i_1754_, v_acc_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03c3_1757_, lean_object* v_00_u03b1_1758_, lean_object* v_00_u03b2_1759_, lean_object* v_f_1760_, lean_object* v_keys_1761_, lean_object* v_vals_1762_, lean_object* v_heq_1763_, lean_object* v_i_1764_, lean_object* v_acc_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_Theorems_getOrigins_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03c3_1757_, v_00_u03b1_1758_, v_00_u03b2_1759_, v_f_1760_, v_keys_1761_, v_vals_1762_, v_heq_1763_, v_i_1764_, v_acc_1765_);
lean_dec_ref(v_vals_1762_);
lean_dec_ref(v_keys_1761_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty(lean_object* v_00_u03b1_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__3);
return v___x_1768_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0(void){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instEmptyCollectionTheorems(lean_object* v_00_u03b1_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_obj_once(&l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0, &l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0_once, _init_l_Lean_Meta_Grind_instEmptyCollectionTheorems___closed__0);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
if (lean_obj_tag(v_a_1772_) == 0)
{
lean_object* v___x_1774_; 
v___x_1774_ = l_List_reverse___redArg(v_a_1773_);
return v___x_1774_;
}
else
{
lean_object* v_head_1775_; lean_object* v_tail_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1785_; 
v_head_1775_ = lean_ctor_get(v_a_1772_, 0);
v_tail_1776_ = lean_ctor_get(v_a_1772_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1778_ = v_a_1772_;
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_tail_1776_);
lean_inc(v_head_1775_);
lean_dec(v_a_1772_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1785_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = l_Lean_mkLevelParam(v_head_1775_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 1, v_a_1773_);
lean_ctor_set(v___x_1778_, 0, v___x_1780_);
v___x_1782_ = v___x_1778_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_a_1773_);
v___x_1782_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
v_a_1772_ = v_tail_1776_;
v_a_1773_ = v___x_1782_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1786_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
lean_ctor_set(v___x_1791_, 2, v___x_1790_);
lean_ctor_set(v___x_1791_, 3, v___x_1790_);
lean_ctor_set(v___x_1791_, 4, v___x_1789_);
lean_ctor_set(v___x_1791_, 5, v___x_1789_);
lean_ctor_set(v___x_1791_, 6, v___x_1789_);
lean_ctor_set(v___x_1791_, 7, v___x_1789_);
lean_ctor_set(v___x_1791_, 8, v___x_1789_);
lean_ctor_set(v___x_1791_, 9, v___x_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = lean_unsigned_to_nat(32u);
v___x_1793_ = lean_mk_empty_array_with_capacity(v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1795_ = ((size_t)5ULL);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = lean_unsigned_to_nat(32u);
v___x_1798_ = lean_mk_empty_array_with_capacity(v___x_1797_);
v___x_1799_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1800_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___x_1798_);
lean_ctor_set(v___x_1800_, 2, v___x_1796_);
lean_ctor_set(v___x_1800_, 3, v___x_1796_);
lean_ctor_set_usize(v___x_1800_, 4, v___x_1795_);
return v___x_1800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1801_ = lean_box(1);
v___x_1802_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1803_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
lean_ctor_set(v___x_1804_, 1, v___x_1802_);
lean_ctor_set(v___x_1804_, 2, v___x_1801_);
return v___x_1804_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
return v___x_1813_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1819_ = l_Lean_stringToMessageData(v___x_1818_);
return v___x_1819_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1822_ = l_Lean_stringToMessageData(v___x_1821_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1825_ = l_Lean_stringToMessageData(v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1826_, lean_object* v_declHint_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; lean_object* v_env_1831_; uint8_t v___y_1833_; uint8_t v___x_1889_; uint8_t v___x_1890_; 
v___x_1830_ = lean_st_ref_get(v___y_1828_);
v_env_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc_ref(v_env_1831_);
lean_dec(v___x_1830_);
v___x_1889_ = l_Lean_Name_isAnonymous(v_declHint_1827_);
v___x_1890_ = lean_bool_not(v___x_1889_);
if (v___x_1890_ == 0)
{
v___y_1833_ = v___x_1890_;
goto v___jp_1832_;
}
else
{
uint8_t v_isExporting_1891_; 
v_isExporting_1891_ = lean_ctor_get_uint8(v_env_1831_, sizeof(void*)*8);
v___y_1833_ = v_isExporting_1891_;
goto v___jp_1832_;
}
v___jp_1832_:
{
if (v___y_1833_ == 0)
{
lean_object* v___x_1834_; 
lean_dec_ref(v_env_1831_);
lean_dec(v_declHint_1827_);
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v_msg_1826_);
return v___x_1834_;
}
else
{
uint8_t v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = 0;
lean_inc_ref(v_env_1831_);
v___x_1836_ = l_Lean_Environment_setExporting(v_env_1831_, v___x_1835_);
lean_inc(v_declHint_1827_);
lean_inc_ref(v___x_1836_);
v___x_1837_ = l_Lean_Environment_contains(v___x_1836_, v_declHint_1827_, v___y_1833_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
lean_dec_ref(v___x_1836_);
lean_dec_ref(v_env_1831_);
lean_dec(v_declHint_1827_);
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v_msg_1826_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v_c_1844_; lean_object* v___x_1845_; 
v___x_1839_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1840_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1841_ = l_Lean_Options_empty;
v___x_1842_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1836_);
lean_ctor_set(v___x_1842_, 1, v___x_1839_);
lean_ctor_set(v___x_1842_, 2, v___x_1840_);
lean_ctor_set(v___x_1842_, 3, v___x_1841_);
lean_inc(v_declHint_1827_);
v___x_1843_ = l_Lean_MessageData_ofConstName(v_declHint_1827_, v___x_1835_);
v_c_1844_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1844_, 0, v___x_1842_);
lean_ctor_set(v_c_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1831_, v_declHint_1827_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec_ref(v_env_1831_);
lean_dec(v_declHint_1827_);
v___x_1846_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
lean_ctor_set(v___x_1847_, 1, v_c_1844_);
v___x_1848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = l_Lean_MessageData_note(v___x_1849_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v_msg_1826_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
else
{
lean_object* v_val_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1888_; 
v_val_1853_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1855_ = v___x_1845_;
v_isShared_1856_ = v_isSharedCheck_1888_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_val_1853_);
lean_dec(v___x_1845_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1888_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v_mod_1860_; uint8_t v___x_1861_; 
v___x_1857_ = lean_box(0);
v___x_1858_ = l_Lean_Environment_header(v_env_1831_);
lean_dec_ref(v_env_1831_);
v___x_1859_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1858_);
v_mod_1860_ = lean_array_get(v___x_1857_, v___x_1859_, v_val_1853_);
lean_dec(v_val_1853_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = l_Lean_isPrivateName(v_declHint_1827_);
lean_dec(v_declHint_1827_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1862_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v_c_1844_);
v___x_1864_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = l_Lean_MessageData_ofName(v_mod_1860_);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = l_Lean_MessageData_note(v___x_1869_);
v___x_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1871_, 0, v_msg_1826_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1871_);
v___x_1873_ = v___x_1855_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v_c_1844_);
v___x_1877_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = l_Lean_MessageData_ofName(v_mod_1860_);
v___x_1880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l_Lean_MessageData_note(v___x_1882_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_msg_1826_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1884_);
v___x_1886_ = v___x_1855_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1892_, lean_object* v_declHint_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_1892_, v_declHint_1893_, v___y_1894_);
lean_dec(v___y_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_1897_, lean_object* v_declHint_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1914_; 
v___x_1904_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_1897_, v_declHint_1898_, v___y_1902_);
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1914_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1914_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1909_ = l_Lean_unknownIdentifierMessageTag;
v___x_1910_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v_a_1905_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1910_);
v___x_1912_ = v___x_1907_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_1915_, lean_object* v_declHint_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_1915_, v_declHint_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_1923_, lean_object* v_msg_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_fileName_1930_; lean_object* v_fileMap_1931_; lean_object* v_options_1932_; lean_object* v_currRecDepth_1933_; lean_object* v_maxRecDepth_1934_; lean_object* v_ref_1935_; lean_object* v_currNamespace_1936_; lean_object* v_openDecls_1937_; lean_object* v_initHeartbeats_1938_; lean_object* v_maxHeartbeats_1939_; lean_object* v_quotContext_1940_; lean_object* v_currMacroScope_1941_; uint8_t v_diag_1942_; lean_object* v_cancelTk_x3f_1943_; uint8_t v_suppressElabErrors_1944_; lean_object* v_inheritedTraceOptions_1945_; lean_object* v_ref_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v_fileName_1930_ = lean_ctor_get(v___y_1927_, 0);
v_fileMap_1931_ = lean_ctor_get(v___y_1927_, 1);
v_options_1932_ = lean_ctor_get(v___y_1927_, 2);
v_currRecDepth_1933_ = lean_ctor_get(v___y_1927_, 3);
v_maxRecDepth_1934_ = lean_ctor_get(v___y_1927_, 4);
v_ref_1935_ = lean_ctor_get(v___y_1927_, 5);
v_currNamespace_1936_ = lean_ctor_get(v___y_1927_, 6);
v_openDecls_1937_ = lean_ctor_get(v___y_1927_, 7);
v_initHeartbeats_1938_ = lean_ctor_get(v___y_1927_, 8);
v_maxHeartbeats_1939_ = lean_ctor_get(v___y_1927_, 9);
v_quotContext_1940_ = lean_ctor_get(v___y_1927_, 10);
v_currMacroScope_1941_ = lean_ctor_get(v___y_1927_, 11);
v_diag_1942_ = lean_ctor_get_uint8(v___y_1927_, sizeof(void*)*14);
v_cancelTk_x3f_1943_ = lean_ctor_get(v___y_1927_, 12);
v_suppressElabErrors_1944_ = lean_ctor_get_uint8(v___y_1927_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1945_ = lean_ctor_get(v___y_1927_, 13);
v_ref_1946_ = l_Lean_replaceRef(v_ref_1923_, v_ref_1935_);
lean_inc_ref(v_inheritedTraceOptions_1945_);
lean_inc(v_cancelTk_x3f_1943_);
lean_inc(v_currMacroScope_1941_);
lean_inc(v_quotContext_1940_);
lean_inc(v_maxHeartbeats_1939_);
lean_inc(v_initHeartbeats_1938_);
lean_inc(v_openDecls_1937_);
lean_inc(v_currNamespace_1936_);
lean_inc(v_maxRecDepth_1934_);
lean_inc(v_currRecDepth_1933_);
lean_inc_ref(v_options_1932_);
lean_inc_ref(v_fileMap_1931_);
lean_inc_ref(v_fileName_1930_);
v___x_1947_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1947_, 0, v_fileName_1930_);
lean_ctor_set(v___x_1947_, 1, v_fileMap_1931_);
lean_ctor_set(v___x_1947_, 2, v_options_1932_);
lean_ctor_set(v___x_1947_, 3, v_currRecDepth_1933_);
lean_ctor_set(v___x_1947_, 4, v_maxRecDepth_1934_);
lean_ctor_set(v___x_1947_, 5, v_ref_1946_);
lean_ctor_set(v___x_1947_, 6, v_currNamespace_1936_);
lean_ctor_set(v___x_1947_, 7, v_openDecls_1937_);
lean_ctor_set(v___x_1947_, 8, v_initHeartbeats_1938_);
lean_ctor_set(v___x_1947_, 9, v_maxHeartbeats_1939_);
lean_ctor_set(v___x_1947_, 10, v_quotContext_1940_);
lean_ctor_set(v___x_1947_, 11, v_currMacroScope_1941_);
lean_ctor_set(v___x_1947_, 12, v_cancelTk_x3f_1943_);
lean_ctor_set(v___x_1947_, 13, v_inheritedTraceOptions_1945_);
lean_ctor_set_uint8(v___x_1947_, sizeof(void*)*14, v_diag_1942_);
lean_ctor_set_uint8(v___x_1947_, sizeof(void*)*14 + 1, v_suppressElabErrors_1944_);
v___x_1948_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v_msg_1924_, v___y_1925_, v___y_1926_, v___x_1947_, v___y_1928_);
lean_dec_ref_known(v___x_1947_, 14);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1949_, lean_object* v_msg_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_1949_, v_msg_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v_ref_1949_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_1957_, lean_object* v_msg_1958_, lean_object* v_declHint_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v_a_1966_; lean_object* v___x_1967_; 
v___x_1965_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_1958_, v_declHint_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_1957_, v_a_1966_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_1968_, lean_object* v_msg_1969_, lean_object* v_declHint_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1968_, v_msg_1969_, v_declHint_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v_ref_1968_);
return v_res_1976_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1979_ = l_Lean_stringToMessageData(v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1980_, lean_object* v_constName_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1987_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1988_ = 0;
lean_inc(v_constName_1981_);
v___x_1989_ = l_Lean_MessageData_ofConstName(v_constName_1981_, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1987_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Theorems_eraseDecl___redArg___lam__0___closed__1);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1980_, v___x_1992_, v_constName_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1994_, lean_object* v_constName_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_1994_, v_constName_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v_ref_1994_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(lean_object* v_constName_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_ref_2008_; lean_object* v___x_2009_; 
v_ref_2008_ = lean_ctor_get(v___y_2005_, 5);
v___x_2009_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_2008_, v_constName_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(lean_object* v_constName_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; lean_object* v_env_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; 
v___x_2023_ = lean_st_ref_get(v___y_2021_);
v_env_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc_ref(v_env_2024_);
lean_dec(v___x_2023_);
v___x_2025_ = 0;
lean_inc(v_constName_2017_);
v___x_2026_ = l_Lean_Environment_findConstVal_x3f(v_env_2024_, v_constName_2017_, v___x_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
return v___x_2027_;
}
else
{
lean_object* v_val_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_constName_2017_);
v_val_2028_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2026_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_val_2028_);
lean_dec(v___x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 0);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_val_2028_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0___boxed(lean_object* v_constName_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(v_constName_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
return v_res_2042_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofForDecl___closed__1(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = ((lean_object*)(l_Lean_Meta_Grind_getProofForDecl___closed__0));
v___x_2045_ = l_Lean_stringToMessageData(v___x_2044_);
return v___x_2045_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getProofForDecl___closed__3(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l_Lean_Meta_Grind_getProofForDecl___closed__2));
v___x_2048_ = l_Lean_stringToMessageData(v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofForDecl(lean_object* v_declName_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v___x_2055_; 
lean_inc(v_declName_2049_);
v___x_2055_ = l_Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0(v_declName_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2098_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2098_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2098_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2068_; lean_object* v_env_2069_; uint8_t v___x_2070_; 
v___x_2068_ = lean_st_ref_get(v_a_2053_);
v_env_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc_ref(v_env_2069_);
lean_dec(v___x_2068_);
lean_inc(v_declName_2049_);
v___x_2070_ = l_Lean_wasOriginallyTheorem(v_env_2069_, v_declName_2049_);
if (v___x_2070_ == 0)
{
lean_object* v_type_2071_; lean_object* v___x_2072_; 
v_type_2071_ = lean_ctor_get(v_a_2056_, 2);
lean_inc_ref(v_type_2071_);
v___x_2072_ = l_Lean_Meta_isProp(v_type_2071_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; uint8_t v___x_2074_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
v___x_2074_ = lean_unbox(v_a_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; uint8_t v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_del_object(v___x_2058_);
lean_dec(v_a_2056_);
v___x_2075_ = lean_obj_once(&l_Lean_Meta_Grind_getProofForDecl___closed__1, &l_Lean_Meta_Grind_getProofForDecl___closed__1_once, _init_l_Lean_Meta_Grind_getProofForDecl___closed__1);
v___x_2076_ = lean_unbox(v_a_2073_);
lean_dec(v_a_2073_);
v___x_2077_ = l_Lean_MessageData_ofConstName(v_declName_2049_, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2075_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_obj_once(&l_Lean_Meta_Grind_getProofForDecl___closed__3, &l_Lean_Meta_Grind_getProofForDecl___closed__3_once, _init_l_Lean_Meta_Grind_getProofForDecl___closed__3);
v___x_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2078_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = l_Lean_throwError___at___00Lean_Meta_Grind_Theorems_eraseDecl_spec__0___redArg(v___x_2080_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
else
{
lean_dec(v_a_2073_);
goto v___jp_2060_;
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_del_object(v___x_2058_);
lean_dec(v_a_2056_);
lean_dec(v_declName_2049_);
v_a_2090_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2072_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2072_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
else
{
goto v___jp_2060_;
}
v___jp_2060_:
{
lean_object* v_levelParams_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v_levelParams_2061_ = lean_ctor_get(v_a_2056_, 1);
lean_inc(v_levelParams_2061_);
lean_dec(v_a_2056_);
v___x_2062_ = lean_box(0);
v___x_2063_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_getProofForDecl_spec__1(v_levelParams_2061_, v___x_2062_);
v___x_2064_ = l_Lean_mkConst(v_declName_2049_, v___x_2063_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2064_);
v___x_2066_ = v___x_2058_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_declName_2049_);
v_a_2099_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2055_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2055_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getProofForDecl___boxed(lean_object* v_declName_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_Meta_Grind_getProofForDecl(v_declName_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(lean_object* v_00_u03b1_2114_, lean_object* v_constName_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___redArg(v_constName_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2122_, lean_object* v_constName_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0(v_00_u03b1_2122_, v_constName_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2130_, lean_object* v_ref_2131_, lean_object* v_constName_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___redArg(v_ref_2131_, v_constName_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2139_, lean_object* v_ref_2140_, lean_object* v_constName_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1(v_00_u03b1_2139_, v_ref_2140_, v_constName_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v_ref_2140_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2148_, lean_object* v_ref_2149_, lean_object* v_msg_2150_, lean_object* v_declHint_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2149_, v_msg_2150_, v_declHint_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2158_, lean_object* v_ref_2159_, lean_object* v_msg_2160_, lean_object* v_declHint_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2158_, v_ref_2159_, v_msg_2160_, v_declHint_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v_ref_2159_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2168_, lean_object* v_declHint_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2168_, v_declHint_2169_, v___y_2173_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2176_, lean_object* v_declHint_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2176_, v_declHint_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2184_, lean_object* v_ref_2185_, lean_object* v_msg_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2185_, v_msg_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2193_, lean_object* v_ref_2194_, lean_object* v_msg_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Grind_getProofForDecl_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2193_, v_ref_2194_, v_msg_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v_ref_2194_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(lean_object* v___x_2202_, lean_object* v_s_2203_, lean_object* v_sym_2204_, lean_object* v___x_2205_, lean_object* v___x_2206_, lean_object* v_next_2207_, lean_object* v_acc_2208_, lean_object* v_h_2209_, lean_object* v_G_2210_){
_start:
{
uint8_t v___x_2211_; 
v___x_2211_ = lean_nat_dec_lt(v_next_2207_, v___x_2202_);
if (v___x_2211_ == 0)
{
lean_dec_ref(v_G_2210_);
lean_dec_ref(v___x_2206_);
lean_dec(v_sym_2204_);
lean_dec_ref(v_s_2203_);
lean_inc_ref(v_acc_2208_);
return v_acc_2208_;
}
else
{
lean_object* v___x_2212_; lean_object* v_smap_2213_; lean_object* v_origins_2214_; lean_object* v_erased_2215_; lean_object* v_omap_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2242_; 
v___x_2212_ = lean_array_fget(v_s_2203_, v_next_2207_);
v_smap_2213_ = lean_ctor_get(v___x_2212_, 0);
v_origins_2214_ = lean_ctor_get(v___x_2212_, 1);
v_erased_2215_ = lean_ctor_get(v___x_2212_, 2);
v_omap_2216_ = lean_ctor_get(v___x_2212_, 3);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2218_ = v___x_2212_;
v_isShared_2219_ = v_isSharedCheck_2242_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_omap_2216_);
lean_inc(v_erased_2215_);
lean_inc(v_origins_2214_);
lean_inc(v_smap_2213_);
lean_dec(v___x_2212_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2242_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__15));
v___x_2221_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___redArg___closed__16));
lean_inc(v_sym_2204_);
v___x_2222_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_2220_, v___x_2221_, v_smap_2213_, v_sym_2204_);
if (lean_obj_tag(v___x_2222_) == 1)
{
lean_object* v_val_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v_G_2210_);
lean_dec_ref(v___x_2206_);
v_val_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2238_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_val_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2238_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2227_ = l_Lean_PersistentHashMap_erase___redArg(v___x_2220_, v___x_2221_, v_smap_2213_, v_sym_2204_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2227_);
v___x_2229_ = v___x_2218_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_origins_2214_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_erased_2215_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_omap_2216_);
v___x_2229_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2230_ = lean_array_fset(v_s_2203_, v_next_2207_, v___x_2229_);
v___x_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2231_, 0, v_val_2223_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2231_);
v___x_2233_ = v___x_2225_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v___x_2205_);
return v___x_2235_;
}
}
}
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_dec(v___x_2222_);
lean_del_object(v___x_2218_);
lean_dec_ref(v_omap_2216_);
lean_dec_ref(v_erased_2215_);
lean_dec_ref(v_origins_2214_);
lean_dec_ref(v_smap_2213_);
lean_dec(v_sym_2204_);
lean_dec_ref(v_s_2203_);
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = lean_nat_add(v_next_2207_, v___x_2239_);
v___x_2241_ = lean_apply_4(v_G_2210_, v___x_2240_, v___x_2206_, lean_box(0), lean_box(0));
return v___x_2241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed(lean_object* v___x_2243_, lean_object* v_s_2244_, lean_object* v_sym_2245_, lean_object* v___x_2246_, lean_object* v___x_2247_, lean_object* v_next_2248_, lean_object* v_acc_2249_, lean_object* v_h_2250_, lean_object* v_G_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0(v___x_2243_, v_s_2244_, v_sym_2245_, v___x_2246_, v___x_2247_, v_next_2248_, v_acc_2249_, v_h_2250_, v_G_2251_);
lean_dec_ref(v_acc_2249_);
lean_dec(v_next_2248_);
lean_dec(v___x_2243_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(lean_object* v_s_2256_, lean_object* v_sym_2257_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; lean_object* v_fst_2265_; 
v___x_2258_ = lean_array_get_size(v_s_2256_);
v___x_2259_ = lean_unsigned_to_nat(0u);
v___x_2260_ = lean_box(0);
v___x_2261_ = lean_box(0);
v___x_2262_ = ((lean_object*)(l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___closed__0));
v___f_2263_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg___lam__0___boxed), 9, 5);
lean_closure_set(v___f_2263_, 0, v___x_2258_);
lean_closure_set(v___f_2263_, 1, v_s_2256_);
lean_closure_set(v___f_2263_, 2, v_sym_2257_);
lean_closure_set(v___f_2263_, 3, v___x_2261_);
lean_closure_set(v___f_2263_, 4, v___x_2262_);
v___x_2264_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2263_, v___x_2259_, v___x_2262_, lean_box(0));
v_fst_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_fst_2265_);
lean_dec(v___x_2264_);
if (lean_obj_tag(v_fst_2265_) == 0)
{
return v___x_2260_;
}
else
{
lean_object* v_val_2266_; 
v_val_2266_ = lean_ctor_get(v_fst_2265_, 0);
lean_inc(v_val_2266_);
lean_dec_ref_known(v_fst_2265_, 1);
return v_val_2266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f(lean_object* v_00_u03b1_2267_, lean_object* v_s_2268_, lean_object* v_sym_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Meta_Grind_TheoremsArray_retrieve_x3f___redArg(v_s_2268_, v_sym_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0(void){
_start:
{
lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; 
v___f_2271_ = ((lean_object*)(l_Lean_Meta_Grind_instHashableOrigin___closed__0));
v___f_2272_ = ((lean_object*)(l_Lean_Meta_Grind_instBEqOrigin___closed__0));
v___x_2273_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___f_2272_, v___f_2271_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v_thms_2276_; 
v___x_2274_ = lean_obj_once(&l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0, &l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0_once, _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__0);
v___x_2275_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1, &l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedTheorems_default___closed__1);
v_thms_2276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_thms_2276_, 0, v___x_2275_);
lean_ctor_set(v_thms_2276_, 1, v___x_2274_);
lean_ctor_set(v_thms_2276_, 2, v___x_2274_);
lean_ctor_set(v_thms_2276_, 3, v___x_2275_);
return v_thms_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert___redArg(lean_object* v_inst_2277_, lean_object* v_s_2278_, lean_object* v_thm_2279_){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v___x_2280_ = lean_array_get_size(v_s_2278_);
v___x_2281_ = lean_unsigned_to_nat(0u);
v___x_2282_ = lean_nat_dec_eq(v___x_2280_, v___x_2281_);
if (v___x_2282_ == 0)
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_nat_dec_lt(v___x_2281_, v___x_2280_);
if (v___x_2283_ == 0)
{
lean_dec(v_thm_2279_);
lean_dec_ref(v_inst_2277_);
return v_s_2278_;
}
else
{
lean_object* v_v_2284_; lean_object* v___x_2285_; lean_object* v_xs_x27_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_v_2284_ = lean_array_fget(v_s_2278_, v___x_2281_);
v___x_2285_ = lean_box(0);
v_xs_x27_2286_ = lean_array_fset(v_s_2278_, v___x_2281_, v___x_2285_);
v___x_2287_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_2277_, v_v_2284_, v_thm_2279_);
v___x_2288_ = lean_array_fset(v_xs_x27_2286_, v___x_2281_, v___x_2287_);
return v___x_2288_;
}
}
else
{
lean_object* v_thms_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec_ref(v_s_2278_);
v_thms_2289_ = lean_obj_once(&l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1, &l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1_once, _init_l_Lean_Meta_Grind_TheoremsArray_insert___redArg___closed__1);
v___x_2290_ = l_Lean_Meta_Grind_Theorems_insert___redArg(v_inst_2277_, v_thms_2289_, v_thm_2279_);
v___x_2291_ = lean_unsigned_to_nat(1u);
v___x_2292_ = lean_mk_empty_array_with_capacity(v___x_2291_);
v___x_2293_ = lean_array_push(v___x_2292_, v___x_2290_);
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_insert(lean_object* v_00_u03b1_2294_, lean_object* v_inst_2295_, lean_object* v_s_2296_, lean_object* v_thm_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_Meta_Grind_TheoremsArray_insert___redArg(v_inst_2295_, v_s_2296_, v_thm_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(lean_object* v_origin_2299_, lean_object* v_as_2300_, size_t v_i_2301_, size_t v_stop_2302_){
_start:
{
uint8_t v___x_2303_; 
v___x_2303_ = lean_usize_dec_eq(v_i_2301_, v_stop_2302_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; lean_object* v_erased_2305_; uint8_t v___x_2306_; 
v___x_2304_ = lean_array_uget_borrowed(v_as_2300_, v_i_2301_);
v_erased_2305_ = lean_ctor_get(v___x_2304_, 2);
v___x_2306_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Theorems_contains_spec__0___redArg(v_erased_2305_, v_origin_2299_);
if (v___x_2306_ == 0)
{
size_t v___x_2307_; size_t v___x_2308_; 
v___x_2307_ = ((size_t)1ULL);
v___x_2308_ = lean_usize_add(v_i_2301_, v___x_2307_);
v_i_2301_ = v___x_2308_;
goto _start;
}
else
{
return v___x_2306_;
}
}
else
{
uint8_t v___x_2310_; 
v___x_2310_ = 0;
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg___boxed(lean_object* v_origin_2311_, lean_object* v_as_2312_, lean_object* v_i_2313_, lean_object* v_stop_2314_){
_start:
{
size_t v_i_boxed_2315_; size_t v_stop_boxed_2316_; uint8_t v_res_2317_; lean_object* v_r_2318_; 
v_i_boxed_2315_ = lean_unbox_usize(v_i_2313_);
lean_dec(v_i_2313_);
v_stop_boxed_2316_ = lean_unbox_usize(v_stop_2314_);
lean_dec(v_stop_2314_);
v_res_2317_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2311_, v_as_2312_, v_i_boxed_2315_, v_stop_boxed_2316_);
lean_dec_ref(v_as_2312_);
lean_dec_ref(v_origin_2311_);
v_r_2318_ = lean_box(v_res_2317_);
return v_r_2318_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(lean_object* v_s_2319_, lean_object* v_origin_2320_){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = lean_array_get_size(v_s_2319_);
v___x_2323_ = lean_nat_dec_lt(v___x_2321_, v___x_2322_);
if (v___x_2323_ == 0)
{
return v___x_2323_;
}
else
{
if (v___x_2323_ == 0)
{
return v___x_2323_;
}
else
{
size_t v___x_2324_; size_t v___x_2325_; uint8_t v___x_2326_; 
v___x_2324_ = ((size_t)0ULL);
v___x_2325_ = lean_usize_of_nat(v___x_2322_);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2320_, v_s_2319_, v___x_2324_, v___x_2325_);
return v___x_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___redArg___boxed(lean_object* v_s_2327_, lean_object* v_origin_2328_){
_start:
{
uint8_t v_res_2329_; lean_object* v_r_2330_; 
v_res_2329_ = l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(v_s_2327_, v_origin_2328_);
lean_dec_ref(v_origin_2328_);
lean_dec_ref(v_s_2327_);
v_r_2330_ = lean_box(v_res_2329_);
return v_r_2330_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_TheoremsArray_isErased(lean_object* v_00_u03b1_2331_, lean_object* v_s_2332_, lean_object* v_origin_2333_){
_start:
{
uint8_t v___x_2334_; 
v___x_2334_ = l_Lean_Meta_Grind_TheoremsArray_isErased___redArg(v_s_2332_, v_origin_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_isErased___boxed(lean_object* v_00_u03b1_2335_, lean_object* v_s_2336_, lean_object* v_origin_2337_){
_start:
{
uint8_t v_res_2338_; lean_object* v_r_2339_; 
v_res_2338_ = l_Lean_Meta_Grind_TheoremsArray_isErased(v_00_u03b1_2335_, v_s_2336_, v_origin_2337_);
lean_dec_ref(v_origin_2337_);
lean_dec_ref(v_s_2336_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(lean_object* v_00_u03b1_2340_, lean_object* v_origin_2341_, lean_object* v_as_2342_, size_t v_i_2343_, size_t v_stop_2344_){
_start:
{
uint8_t v___x_2345_; 
v___x_2345_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___redArg(v_origin_2341_, v_as_2342_, v_i_2343_, v_stop_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0___boxed(lean_object* v_00_u03b1_2346_, lean_object* v_origin_2347_, lean_object* v_as_2348_, lean_object* v_i_2349_, lean_object* v_stop_2350_){
_start:
{
size_t v_i_boxed_2351_; size_t v_stop_boxed_2352_; uint8_t v_res_2353_; lean_object* v_r_2354_; 
v_i_boxed_2351_ = lean_unbox_usize(v_i_2349_);
lean_dec(v_i_2349_);
v_stop_boxed_2352_ = lean_unbox_usize(v_stop_2350_);
lean_dec(v_stop_2350_);
v_res_2353_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_TheoremsArray_isErased_spec__0(v_00_u03b1_2346_, v_origin_2347_, v_as_2348_, v_i_boxed_2351_, v_stop_boxed_2352_);
lean_dec_ref(v_as_2348_);
lean_dec_ref(v_origin_2347_);
v_r_2354_ = lean_box(v_res_2353_);
return v_r_2354_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(lean_object* v_upperBound_2355_, lean_object* v_s_2356_, lean_object* v_origin_2357_, lean_object* v_a_2358_, lean_object* v_b_2359_){
_start:
{
lean_object* v_a_2361_; uint8_t v___x_2365_; 
v___x_2365_ = lean_nat_dec_lt(v_a_2358_, v_upperBound_2355_);
if (v___x_2365_ == 0)
{
lean_dec(v_a_2358_);
return v_b_2359_;
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2366_ = lean_array_fget_borrowed(v_s_2356_, v_a_2358_);
v___x_2367_ = l_Lean_Meta_Grind_Theorems_find___redArg(v___x_2366_, v_origin_2357_);
v___x_2368_ = l_List_isEmpty___redArg(v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; 
v___x_2369_ = l_List_appendTR___redArg(v_b_2359_, v___x_2367_);
v_a_2361_ = v___x_2369_;
goto v___jp_2360_;
}
else
{
lean_dec(v___x_2367_);
v_a_2361_ = v_b_2359_;
goto v___jp_2360_;
}
}
v___jp_2360_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = lean_unsigned_to_nat(1u);
v___x_2363_ = lean_nat_add(v_a_2358_, v___x_2362_);
lean_dec(v_a_2358_);
v_a_2358_ = v___x_2363_;
v_b_2359_ = v_a_2361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg___boxed(lean_object* v_upperBound_2370_, lean_object* v_s_2371_, lean_object* v_origin_2372_, lean_object* v_a_2373_, lean_object* v_b_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v_upperBound_2370_, v_s_2371_, v_origin_2372_, v_a_2373_, v_b_2374_);
lean_dec_ref(v_origin_2372_);
lean_dec_ref(v_s_2371_);
lean_dec(v_upperBound_2370_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg(lean_object* v_s_2376_, lean_object* v_origin_2377_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v_r_2380_; lean_object* v___x_2381_; 
v___x_2378_ = lean_array_get_size(v_s_2376_);
v___x_2379_ = lean_unsigned_to_nat(0u);
v_r_2380_ = lean_box(0);
v___x_2381_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v___x_2378_, v_s_2376_, v_origin_2377_, v___x_2379_, v_r_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___redArg___boxed(lean_object* v_s_2382_, lean_object* v_origin_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Meta_Grind_TheoremsArray_find___redArg(v_s_2382_, v_origin_2383_);
lean_dec_ref(v_origin_2383_);
lean_dec_ref(v_s_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find(lean_object* v_00_u03b1_2385_, lean_object* v_s_2386_, lean_object* v_origin_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Meta_Grind_TheoremsArray_find___redArg(v_s_2386_, v_origin_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_TheoremsArray_find___boxed(lean_object* v_00_u03b1_2389_, lean_object* v_s_2390_, lean_object* v_origin_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_Meta_Grind_TheoremsArray_find(v_00_u03b1_2389_, v_s_2390_, v_origin_2391_);
lean_dec_ref(v_origin_2391_);
lean_dec_ref(v_s_2390_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(lean_object* v_00_u03b1_2393_, lean_object* v_upperBound_2394_, lean_object* v_s_2395_, lean_object* v_origin_2396_, lean_object* v_inst_2397_, lean_object* v_R_2398_, lean_object* v_a_2399_, lean_object* v_b_2400_, lean_object* v_c_2401_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___redArg(v_upperBound_2394_, v_s_2395_, v_origin_2396_, v_a_2399_, v_b_2400_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0___boxed(lean_object* v_00_u03b1_2403_, lean_object* v_upperBound_2404_, lean_object* v_s_2405_, lean_object* v_origin_2406_, lean_object* v_inst_2407_, lean_object* v_R_2408_, lean_object* v_a_2409_, lean_object* v_b_2410_, lean_object* v_c_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_TheoremsArray_find_spec__0(v_00_u03b1_2403_, v_upperBound_2404_, v_s_2405_, v_origin_2406_, v_inst_2407_, v_R_2408_, v_a_2409_, v_b_2410_, v_c_2411_);
lean_dec_ref(v_origin_2406_);
lean_dec_ref(v_s_2405_);
lean_dec(v_upperBound_2404_);
return v_res_2412_;
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
